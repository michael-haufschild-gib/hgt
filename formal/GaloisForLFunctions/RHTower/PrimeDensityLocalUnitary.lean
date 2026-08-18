import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert
import GaloisForLFunctions.RHTower.CCMGammaDampedCauchyFrame

/-!
# Prime-density local-unitary invariants are zero-blind

For `σ > 1/2` and a completely multiplicative unimodular `χ : ℕ → ℂ`, the normalized arithmetic
state on `ℓ²(ℕ)` is

```text
Ψ_{σ,χ} = ‖·‖⁻¹ · (n ↦ χ(n) n^{-σ}).
```

This file proves the card's structural content.

* `amp_eq_phase`, `arithState_eq_phase` — the twist acts as a *unimodular phase unitary*
  (`GaloisForLFunctions.HTGeometry.lpPhaseUnitary`), so `Ψ_{σ,χ} = U_χ Ψ_{σ,1}`;
* `norm_arithState` — the state is normalized;
* `twist_eq_prod` — complete multiplicativity plus unique factorization write the twist as a
  product of one-prime phases `χ(p)^{v_p(n)}`: `U_χ` is a *local* (per-prime) unitary;
* `amp_mul`, `amp_bipartition` — the amplitude is completely multiplicative, hence a prime-product
  state: across **every** bipartition of the primes it factors as (part)·(copart), i.e. it has
  Schmidt rank one and zero entanglement.  `primeSetPart` / `primeSetCoPart` generalize the
  threshold-indexed `RHTower.Sieve.SmoothRough.smoothPart` / `roughPart` to an arbitrary prime set,
  which is what an arbitrary bipartition needs;
* `rankOneProj_map`, `rankOneProj_arithState`, `norm_rankOneProj_arithState` — the density operator
  (the corpus's `RHTower.rankOneProj`) is unitarily conjugated by the twist, so every unitary
  invariant — spectrum, rank, purity, Schatten norms, entropies — is `χ`-independent.

The divisor-flexibility half of the card (Helson zeta functions with prescribed zeros and poles
below `Re s = 1`, Bochkov--Romanov / Andersson) is a cited external theorem and is not formalized
here; nothing in this file depends on it.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower.PrimeDensity

open GaloisForLFunctions.HTGeometry

/-- The arithmetic Hilbert space of coefficient sequences. -/
abbrev ArithHilbert : Type := lp (fun _ : ℕ => ℂ) 2

/-- The twisted arithmetic amplitude `χ(n)·n^{-σ}` (zero at `n = 0`). -/
def amp (σ : ℝ) (χ : ℕ → ℂ) (n : ℕ) : ℂ := χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)

theorem amp_zero {σ : ℝ} (hσ : σ ≠ 0) (χ : ℕ → ℂ) : amp σ χ 0 = 0 := by
  rw [amp]
  norm_num [Real.zero_rpow (neg_ne_zero.mpr hσ)]

theorem norm_amp {σ : ℝ} (hσ : 0 < σ) {χ : ℕ → ℂ} (hχ : ∀ n : ℕ, n ≠ 0 → ‖χ n‖ = 1) (n : ℕ) :
    ‖amp σ χ n‖ = ((n : ℝ) ^ (-σ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [amp_zero hσ.ne' χ, norm_zero, Nat.cast_zero,
      Real.zero_rpow (neg_ne_zero.mpr hσ.ne')]
  · rw [amp, norm_mul, hχ n hn, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

theorem memℓp_amp {σ : ℝ} (hσ : 1 / 2 < σ) {χ : ℕ → ℂ} (hχ : ∀ n : ℕ, n ≠ 0 → ‖χ n‖ = 1) :
    Memℓp (amp σ χ) 2 := by
  have hσpos : 0 < σ := lt_trans (by norm_num) hσ
  rw [memℓp_gen_iff (by norm_num)]
  have hsummable : Summable (fun n : ℕ => (((n : ℝ) ^ (2 * σ))⁻¹)) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine hsummable.congr (fun n => ?_)
  rw [ENNReal.toReal_ofNat, norm_amp hσpos hχ n]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσpos.ne'),
      Real.zero_rpow (by positivity : 2 * σ ≠ 0), inv_zero]
    norm_num
  · have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [← Real.rpow_neg hpos.le, ← Real.rpow_mul hpos.le]
    congr 1
    ring

/-- The unimodular completion of a twist (value `1` at `n = 0`). -/
def twistPhase (χ : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 1 else χ n

theorem norm_twistPhase {χ : ℕ → ℂ} (hχ : ∀ n : ℕ, n ≠ 0 → ‖χ n‖ = 1) (n : ℕ) :
    ‖twistPhase χ n‖ = 1 := by
  rw [twistPhase]
  split_ifs with h
  · exact norm_one
  · exact hχ n h

theorem twistPhase_mul_amp {σ : ℝ} (hσ : σ ≠ 0) {χ : ℕ → ℂ} (n : ℕ) :
    twistPhase χ n * amp σ (fun _ => 1) n = amp σ χ n := by
  rw [twistPhase]
  split_ifs with h
  · subst h
    rw [amp_zero hσ (fun _ => 1), amp_zero hσ χ, mul_zero]
  · rw [amp, amp, one_mul]

/-- The normalized arithmetic state. -/
def arithState (σ : ℝ) (hσ : 1 / 2 < σ) (χ : ℕ → ℂ)
    (hχ : ∀ n : ℕ, n ≠ 0 → ‖χ n‖ = 1) : ArithHilbert :=
  (‖(⟨amp σ (fun _ => 1) , memℓp_amp hσ (fun _ _ => norm_one)⟩ : ArithHilbert)‖ : ℂ)⁻¹ •
    (⟨amp σ χ, memℓp_amp hσ hχ⟩ : ArithHilbert)

/-- **The twist is a phase unitary.**  The twisted amplitude is the untwisted one multiplied by a
unimodular sequence. -/
theorem amp_eq_phase (σ : ℝ) (hσ : 1 / 2 < σ) (χ : ℕ → ℂ)
    (hχ : ∀ n : ℕ, n ≠ 0 → ‖χ n‖ = 1) :
    (⟨amp σ χ, memℓp_amp hσ hχ⟩ : ArithHilbert)
      = lpPhaseUnitary (twistPhase χ) (norm_twistPhase hχ)
          (⟨amp σ (fun _ => 1), memℓp_amp hσ (fun _ _ => norm_one)⟩ : ArithHilbert) := by
  refine lp.ext (funext fun n => ?_)
  have hσ0 : σ ≠ 0 := by
    intro h
    rw [h] at hσ
    norm_num at hσ
  exact (twistPhase_mul_amp hσ0 n).symm

/-- **The state is a phase rotation of the untwisted state.** -/
theorem arithState_eq_phase (σ : ℝ) (hσ : 1 / 2 < σ) (χ : ℕ → ℂ)
    (hχ : ∀ n : ℕ, n ≠ 0 → ‖χ n‖ = 1) :
    arithState σ hσ χ hχ
      = lpPhaseUnitary (twistPhase χ) (norm_twistPhase hχ)
          (arithState σ hσ (fun _ => 1) (fun _ _ => norm_one)) := by
  rw [arithState, arithState, amp_eq_phase σ hσ χ hχ, map_smul]

/-! ## Normalization -/

theorem amp_one (σ : ℝ) (χ : ℕ → ℂ) (hχ1 : χ 1 = 1) : amp σ χ 1 = 1 := by
  rw [amp, hχ1, one_mul, Nat.cast_one, Real.one_rpow]
  norm_num

theorem norm_arithState (σ : ℝ) (hσ : 1 / 2 < σ) (χ : ℕ → ℂ)
    (hχ : ∀ n : ℕ, n ≠ 0 → ‖χ n‖ = 1) (hχ1 : χ 1 = 1) :
    ‖arithState σ hσ χ hχ‖ = 1 := by
  set v0 : ArithHilbert := ⟨amp σ (fun _ => 1), memℓp_amp hσ (fun _ _ => norm_one)⟩ with hv0
  have hv0ne : v0 ≠ 0 := by
    intro hcon
    have h1 : (v0 : ℕ → ℂ) 1 = 0 := by rw [hcon]; rfl
    rw [hv0] at h1
    exact one_ne_zero ((amp_one σ (fun _ => 1) rfl).symm.trans h1)
  have hnormpos : 0 < ‖v0‖ := norm_pos_iff.mpr hv0ne
  have heq : ‖(⟨amp σ χ, memℓp_amp hσ hχ⟩ : ArithHilbert)‖ = ‖v0‖ := by
    rw [amp_eq_phase σ hσ χ hχ, hv0]
    exact LinearIsometryEquiv.norm_map _ _
  rw [arithState, norm_smul, heq, ← hv0, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnormpos.ne']

/-! ## Complete multiplicativity: the twist is a product of one-prime phases -/

theorem twist_eq_prod (χ : ℕ →* ℂ) {n : ℕ} (hn : n ≠ 0) :
    χ n = ∏ p ∈ n.primeFactors, (χ p) ^ (n.factorization p) := by
  classical
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, map_prod]
  refine Finset.prod_congr ?_ (fun p _ => map_pow χ p _)
  exact Nat.support_factorization n

/-- **The amplitude is completely multiplicative**: the state is a prime-product state. -/
theorem amp_mul (σ : ℝ) (χ : ℕ →* ℂ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    amp σ (χ : ℕ → ℂ) (m * n) = amp σ (χ : ℕ → ℂ) m * amp σ (χ : ℕ → ℂ) n := by
  have hcast : (((m * n : ℕ) : ℝ) ^ (-σ)) = ((m : ℝ) ^ (-σ)) * ((n : ℝ) ^ (-σ)) := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  rw [amp, amp, amp, map_mul, hcast]
  push_cast
  ring

/-- The `A`-smooth part of `n`. -/
def primeSetPart (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (· ∈ A), p ^ (n.factorization p)

/-- The `A`-rough part of `n`. -/
def primeSetCoPart (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ∉ A), p ^ (n.factorization p)

theorem primeSetPart_mul_primeSetCoPart (A : Set ℕ) [DecidablePred (· ∈ A)] {n : ℕ} (hn : n ≠ 0) :
    primeSetPart A n * primeSetCoPart A n = n := by
  classical
  rw [primeSetPart, primeSetCoPart, Finset.prod_filter_mul_prod_filter_not]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod]
  exact Finset.prod_congr (Nat.support_factorization n).symm (fun _ _ => rfl)

theorem primeSetPart_ne_zero (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : primeSetPart A n ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
  exact pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors
    (Finset.mem_filter.mp hp).1))

theorem primeSetCoPart_ne_zero (A : Set ℕ) [DecidablePred (· ∈ A)] (n : ℕ) : primeSetCoPart A n ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
  exact pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors
    (Finset.mem_filter.mp hp).1))

/-- **Zero entanglement across every prime bipartition.**  The amplitude factors as a product of a
smooth-part amplitude and a rough-part amplitude, so its Schmidt rank across the bipartition is
one. -/
theorem amp_bipartition (σ : ℝ) (χ : ℕ →* ℂ) (A : Set ℕ) [DecidablePred (· ∈ A)] {n : ℕ}
    (hn : n ≠ 0) :
    amp σ (χ : ℕ → ℂ) n
      = amp σ (χ : ℕ → ℂ) (primeSetPart A n) * amp σ (χ : ℕ → ℂ) (primeSetCoPart A n) := by
  conv_lhs => rw [← primeSetPart_mul_primeSetCoPart A hn]
  exact amp_mul σ χ (primeSetPart_ne_zero A n) (primeSetCoPart_ne_zero A n)

/-! ## Unitary conjugacy of the density operator -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

open GaloisForLFunctions.RHTower in
/-- **Unitary conjugacy.**  A phase-rotated state has the unitarily conjugated density.  The
rank-one density `rankOneProj` is the corpus definition from
`RHTower/CCMGammaDampedCauchyFrame.lean`. -/
theorem rankOneProj_map (U : H ≃ₗᵢ[ℂ] H) (Ψ : H) (v : H) :
    rankOneProj (U Ψ) v = U (rankOneProj Ψ (U.symm v)) := by
  rw [rankOneProj, rankOneProj, map_smul]
  have hinner : (inner ℂ (U Ψ) v : ℂ) = inner ℂ Ψ (U.symm v) := by
    rw [← U.inner_map_map Ψ (U.symm v), LinearIsometryEquiv.apply_symm_apply]
  rw [hinner]

/-- **The twisted density is unitarily conjugate to the untwisted one**, so every unitary invariant
— spectrum, rank, purity, Schatten norms, entropies — is independent of the twist. -/
theorem rankOneProj_arithState (σ : ℝ) (hσ : 1 / 2 < σ) (χ : ℕ → ℂ)
    (hχ : ∀ n : ℕ, n ≠ 0 → ‖χ n‖ = 1) (v : ArithHilbert) :
    rankOneProj (arithState σ hσ χ hχ) v
      = lpPhaseUnitary (twistPhase χ) (norm_twistPhase hχ)
          (rankOneProj (arithState σ hσ (fun _ => 1) (fun _ _ => norm_one))
            ((lpPhaseUnitary (twistPhase χ) (norm_twistPhase hχ)).symm v)) := by
  rw [arithState_eq_phase σ hσ χ hχ]
  exact rankOneProj_map _ _ v

/-- The twist changes no norm of the density: the twisted density is the untwisted one read in the
rotated frame. -/
theorem norm_rankOneProj_arithState (σ : ℝ) (hσ : 1 / 2 < σ) (χ : ℕ → ℂ)
    (hχ : ∀ n : ℕ, n ≠ 0 → ‖χ n‖ = 1) (v : ArithHilbert) :
    ‖rankOneProj (arithState σ hσ χ hχ) v‖
      = ‖rankOneProj (arithState σ hσ (fun _ => 1) (fun _ _ => norm_one))
          ((lpPhaseUnitary (twistPhase χ) (norm_twistPhase hχ)).symm v)‖ := by
  rw [rankOneProj_arithState σ hσ χ hχ v]
  exact LinearIsometryEquiv.norm_map _ _

end GaloisForLFunctions.RHTower.PrimeDensity
