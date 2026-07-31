import GaloisForLFunctions.HTGeometry.ExponentialSeedCarrier

/-!
# The block seed and the vanishing of its symbols

For a finite block `B` with steps `step v` the block seed is

`blockSeedFun B step z = ∑_{v ∈ B} exp (exp (2πi z / step v))`,

a sum of one exponential seed per vertex, the `v`-th summand having period `step v`.  Hence the full
block product of difference operators annihilates it, and multiplying a polynomial by the product of
all block variables except one isolates that one summand.

Combined with `symb_eq_zero_of_carrier_const`, a constant carrier therefore forces

`(∏_{j ∈ B ∖ {k}} (exp (t · step j) − 1)) · symb step t P = 0`  for `t = m · 2πi / step k`, `m ≥ 1`.

* `expStepRate` — the rate `2πi / c` whose seed has period `c`;
* `blockSeedFun` — the block seed;
* `seedCarrierPoly_blockSeedFun_isolate` — all but one summand die after multiplying by the
  complementary block product;
* `blockSeed_symb_vanishing` — the resulting symbol equation.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [DecidableEq α]

/-! ### The block seed -/

/-- The exponential rate whose seed has period `c`. -/
def expStepRate (c : ℂ) : ℂ := 2 * Real.pi * Complex.I / c

theorem twoPiI_ne_zero' : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

theorem expStepRate_ne_zero {c : ℂ} (hc : c ≠ 0) : expStepRate c ≠ 0 :=
  div_ne_zero twoPiI_ne_zero' hc

theorem twoPiI_div_expStepRate (c : ℂ) :
    2 * Real.pi * Complex.I / expStepRate c = c := by
  rw [expStepRate, div_div_eq_mul_div, mul_comm (2 * Real.pi * Complex.I : ℂ) c,
    mul_div_assoc, div_self twoPiI_ne_zero', mul_one]

omit [DecidableEq α] in
/-- The seed of a step is annihilated by that step's difference operator. -/
theorem shiftAlgHom_stepVar_expSeed (step : α → ℂ) {v : α} (hv : step v ≠ 0) :
    shiftAlgHom (stepVar step v) (expSeed (expStepRate (step v))) = 0 := by
  have hper := periodic_expSeed (expStepRate_ne_zero hv)
  rw [twoPiI_div_expStepRate] at hper
  funext z
  rw [shiftAlgHom_stepVar]
  show expSeed (expStepRate (step v)) (z + step v) - expSeed (expStepRate (step v)) z = 0
  rw [hper z, sub_self]

/-- **The block seed:** one exponential seed per block vertex. -/
def blockSeedFun (B : Finset α) (step : α → ℂ) : ℂ → ℂ :=
  fun z => ∑ v ∈ B, expSeed (expStepRate (step v)) z

omit [DecidableEq α] in
theorem differentiable_blockSeedFun (B : Finset α) (step : α → ℂ) :
    Differentiable ℂ (blockSeedFun B step) :=
  Differentiable.fun_sum fun _ _ => differentiable_expSeed _

/-- The full block product of difference operators annihilates the block seed. -/
theorem seedAnnihilates_blockSeedFun_prod (B : Finset α) (step : α → ℂ)
    (hne : ∀ v ∈ B, step v ≠ 0) :
    shiftAlgHom (∏ v ∈ B, stepVar step v) (blockSeedFun B step) = 0 := by
  have hzero : ∀ v ∈ B,
      shiftAlgHom (∏ u ∈ B, stepVar step u) (expSeed (expStepRate (step v))) = 0 := by
    intro v hv
    have hfac : (∏ u ∈ B, stepVar step u)
        = (∏ u ∈ B.erase v, stepVar step u) * stepVar step v := by
      rw [mul_comm, Finset.mul_prod_erase B _ hv]
    rw [hfac, map_mul]
    show shiftAlgHom (∏ u ∈ B.erase v, stepVar step u)
      (shiftAlgHom (stepVar step v) (expSeed (expStepRate (step v)))) = 0
    rw [shiftAlgHom_stepVar_expSeed step (hne v hv), map_zero]
  have hfun : blockSeedFun B step = ∑ v ∈ B, expSeed (expStepRate (step v)) := by
    funext w
    rw [Finset.sum_apply]
    rfl
  rw [hfun, map_sum]
  exact Finset.sum_eq_zero hzero

/-! ### Isolating one block -/

/-- After multiplying by the product of the complementary block variables only the `k`-th summand
of the block seed survives. -/
theorem seedCarrierPoly_blockSeedFun_isolate (B : Finset α) (step : α → ℂ)
    (hne : ∀ v ∈ B, step v ≠ 0) {k : α} (hk : k ∈ B) (P : MvPolynomial α ℂ) (z : ℂ) :
    seedCarrierPoly step (blockSeedFun B step) ((∏ j ∈ B.erase k, X j) * P) z
      = seedCarrierPoly step (expSeed (expStepRate (step k))) ((∏ j ∈ B.erase k, X j) * P) z := by
  have hfun : blockSeedFun B step
      = fun w => ∑ v ∈ B, expSeed (expStepRate (step v)) w := rfl
  rw [hfun, seedCarrierPoly_sum]
  rw [← Finset.add_sum_erase B _ hk]
  have hzero : ∀ v ∈ B.erase k,
      seedCarrierPoly step (expSeed (expStepRate (step v))) ((∏ j ∈ B.erase k, X j) * P) z = 0 := by
    intro v hv
    have hfac : (∏ j ∈ B.erase k, X j) * P
        = ((∏ j ∈ (B.erase k).erase v, X j) * P) * X v := by
      rw [← Finset.mul_prod_erase (B.erase k) _ hv]
      ring
    have hz : seedCarrierPoly step (expSeed (expStepRate (step v))) (X v) = 0 := by
      show shiftAlgHom (polyShift step (X v)) (expSeed (expStepRate (step v))) = 0
      rw [polyShift_X, shiftAlgHom_stepVar_expSeed step (hne v (Finset.mem_of_mem_erase hv))]
    rw [hfac, seedCarrierPoly_mul, hz, map_zero]
    rfl
  rw [Finset.sum_eq_zero hzero, add_zero]

/-! ### The symbol equation -/

/-- **A constant block carrier forces the symbol equation.**  Isolating the `k`-th block and using
that `exp` covers the punctured plane, the symbol of the complementary block product times the
symbol of `P` vanishes at every `t = m · 2πi / step k` with `m ≥ 1`. -/
theorem blockSeed_symb_vanishing (B : Finset α) (step : α → ℂ)
    (hne : ∀ v ∈ B, step v ≠ 0) {k : α} (hk : k ∈ B) (P : MvPolynomial α ℂ)
    (hconst : ∀ z z' : ℂ, seedCarrierPoly step (blockSeedFun B step) P z
      = seedCarrierPoly step (blockSeedFun B step) P z')
    {m : ℕ} (hm : 1 ≤ m) :
    (∏ j ∈ B.erase k,
        (Complex.exp ((m : ℂ) * expStepRate (step k) * step j) - 1))
      * symb step ((m : ℂ) * expStepRate (step k)) P = 0 := by
  set D : MvPolynomial α ℂ := ∏ j ∈ B.erase k, X j with hD
  set a := expStepRate (step k) with ha
  have hDconst : ∀ z z' : ℂ,
      seedCarrierPoly step (expSeed a) (D * P) z
        = seedCarrierPoly step (expSeed a) (D * P) z' := by
    have hC : seedCarrierPoly step (blockSeedFun B step) P
        = fun _ => seedCarrierPoly step (blockSeedFun B step) P 0 := by
      funext z
      exact hconst z 0
    intro z z'
    rw [← seedCarrierPoly_blockSeedFun_isolate B step hne hk P z,
      ← seedCarrierPoly_blockSeedFun_isolate B step hne hk P z',
      seedCarrierPoly_mul, hC, shiftAlgHom_const]
  have hsymb := symb_eq_zero_of_carrier_const step (expStepRate_ne_zero (hne k hk)) (D * P)
    hDconst hm
  rw [symb_mul, hD, symb_prod_X] at hsymb
  exact hsymb

end

end GaloisForLFunctions.HTGeometry
