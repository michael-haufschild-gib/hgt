import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicStateFactorization

/-!
# Exact logarithmic transport across the dyadic squarefree channel

`dyadic-squarefree-euler-fock-source-factorization`, §2–§3.

Two things are proved here.

* The **elementary tensor form** of the pointed-state factorization `(7)`: the signed arithmetic
  unitary carries `e_σ` to the honest `ℓ²` vector `s_σ ⊗ e_{2σ}`.
* The **logarithmic transport law** `(9)` and its pointed expectation form `(11)`.  The transport
  law is stated for arbitrary coordinate functions, so no core-domain hypothesis appears; the
  expectation identity `b_σ = a_σ + 2 b_{2σ}` is an identity between honest convergent sums.
-/

open Complex Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Elementary tensors in `ℓ²` -/

theorem memlp_tensor {ι κ : Type*} (x : lp (fun _ : ι => ℂ) 2) (y : lp (fun _ : κ => ℂ) 2) :
    Memℓp (fun q : ι × κ => x q.1 * y q.2) 2 := by
  refine memlp_two_of_summable_sq ?_
  have hx : Summable (fun i : ι => ‖x i‖ ^ (2 : ℕ)) := by
    have h := (memℓp_gen_iff (p := 2) (E := fun _ : ι => ℂ) (by norm_num)).mp (lp.memℓp x)
    refine h.congr fun i => ?_
    rw [← Real.rpow_natCast ‖x i‖ 2]
    norm_num
  have hy : Summable (fun k : κ => ‖y k‖ ^ (2 : ℕ)) := by
    have h := (memℓp_gen_iff (p := 2) (E := fun _ : κ => ℂ) (by norm_num)).mp (lp.memℓp y)
    refine h.congr fun k => ?_
    rw [← Real.rpow_natCast ‖y k‖ 2]
    norm_num
  refine (hx.mul_of_nonneg hy (fun i => by positivity) (fun k => by positivity)).congr fun q => ?_
  rw [norm_mul, mul_pow]

/-- The elementary tensor `x ⊗ y` inside `ℓ²` of the product index. -/
def lpTensor {ι κ : Type*} (x : lp (fun _ : ι => ℂ) 2) (y : lp (fun _ : κ => ℂ) 2) :
    lp (fun _ : ι × κ => ℂ) 2 :=
  ⟨fun q => x q.1 * y q.2, memlp_tensor x y⟩

@[simp] theorem lpTensor_apply {ι κ : Type*} (x : lp (fun _ : ι => ℂ) 2)
    (y : lp (fun _ : κ => ℂ) 2) (q : ι × κ) : lpTensor x y q = x q.1 * y q.2 := rfl

/-- **Equation (7), vector form.**  `U e_σ = s_σ ⊗ e_{2σ}` in `DyadicSquarefreeL2`. -/
theorem dyadicSquarefreeSignedUnitary_eq_tensor {σ : ℝ} (hσ : 1 < σ)
    (hσ2 : 1 < 2 * σ) :
    dyadicSquarefreeSignedUnitary (eulerPointedState hσ)
      = lpTensor (squarefreePointedState hσ) (eulerPointedState hσ2) := by
  refine lp.ext (funext fun q => ?_)
  rw [dyadicSquarefreeSignedUnitary_eulerPointedState hσ q]
  rfl

/-! ## The logarithmic transport law `(9)` -/

/-- The Euler logarithmic observable on raw coordinate functions. -/
def eulerLogMul (f : ℕ+ → ℂ) (n : ℕ+) : ℂ := ((Real.log (n : ℝ) : ℝ) : ℂ) * f n

/-- The signed arithmetic transport on raw coordinate functions. -/
def dyadicSignedTransport (f : ℕ+ → ℂ) (q : SquarefreePNat × ℕ+) : ℂ :=
  dyadicMoebiusPhase q * f (dyadicSquarefreeSquareEquiv.symm q)

theorem dyadicSignedTransport_of_lp (x : EulerPositiveL2) (q : SquarefreePNat × ℕ+) :
    dyadicSquarefreeSignedUnitary x q = dyadicSignedTransport (fun n => x n) q := rfl

/-- **Equation (9).**  Conjugating the Euler logarithmic observable by the signed arithmetic
transport gives `L_sq ⊗ I + 2 · I ⊗ L_E` — the additive splitting `log n = log d + 2 log m` — for
every coordinate function, with no core-domain restriction. -/
theorem dyadicSignedTransport_eulerLogMul (f : ℕ+ → ℂ) (q : SquarefreePNat × ℕ+) :
    dyadicSignedTransport (eulerLogMul f) q
      = ((Real.log ((q.1.1 : ℝ)) : ℝ) : ℂ) * dyadicSignedTransport f q
        + 2 * (((Real.log ((q.2 : ℝ)) : ℝ) : ℂ) * dyadicSignedTransport f q) := by
  have hlog := dyadicSquarefreeSquareEquiv_log (dyadicSquarefreeSquareEquiv.symm q)
  rw [Equiv.apply_symm_apply] at hlog
  rw [dyadicSignedTransport, dyadicSignedTransport, eulerLogMul, hlog]
  push_cast
  ring

/-! ## Logarithmic masses and the pointed mean identity `(11)` -/

theorem summable_pnat_log_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ+ => Real.log (n : ℝ) * (n : ℝ) ^ (-σ)) := by
  set δ : ℝ := (σ - 1) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hσδ : 1 < σ - δ := by rw [hδ]; linarith
  refine Summable.of_nonneg_of_le (g := fun n : ℕ+ => Real.log (n : ℝ) * (n : ℝ) ^ (-σ))
    (f := fun n : ℕ+ => δ⁻¹ * (n : ℝ) ^ (-(σ - δ))) (fun n => ?_) (fun n => ?_)
    ((summable_pnat_rpow hσδ).mul_left δ⁻¹)
  · have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast n.property)
    positivity
  · have hn : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ :=
      Real.log_le_rpow_div (le_of_lt hn) hδpos
    have hstep : Real.log (n : ℝ) * (n : ℝ) ^ (-σ)
        ≤ ((n : ℝ) ^ δ / δ) * (n : ℝ) ^ (-σ) := by
      exact mul_le_mul_of_nonneg_right hlog (by positivity)
    have hcombine : ((n : ℝ) ^ δ / δ) * (n : ℝ) ^ (-σ) = δ⁻¹ * (n : ℝ) ^ (-(σ - δ)) := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hn]
      rw [show δ + -σ = -(σ - δ) by ring, div_eq_inv_mul]
    linarith [hstep, hcombine.le, hcombine.ge]

theorem summable_squarefree_log_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun d : SquarefreePNat => Real.log ((d.1 : ℝ)) * ((d.1 : ℝ)) ^ (-σ)) :=
  (summable_pnat_log_rpow hσ).comp_injective (fun _ _ hab => Subtype.ext hab)

/-- `∑_{n ≥ 1} (log n) n^{-σ}` — the unnormalized Euler logarithmic mass. -/
def eulerLogMass (σ : ℝ) : ℝ := ∑' n : ℕ+, Real.log (n : ℝ) * (n : ℝ) ^ (-σ)

/-- `∑_{d squarefree} (log d) d^{-σ}` — the unnormalized squarefree logarithmic mass. -/
def squarefreeLogMass (σ : ℝ) : ℝ :=
  ∑' d : SquarefreePNat, Real.log ((d.1 : ℝ)) * ((d.1 : ℝ)) ^ (-σ)

/-- `b_σ = ⟨e_σ, L_E e_σ⟩`, the pointed Euler logarithmic mean. -/
def eulerLogMean (σ : ℝ) : ℝ := eulerLogMass σ / eulerMass σ

/-- `a_σ = ⟨s_σ, L_sq s_σ⟩`, the pointed squarefree logarithmic mean. -/
def squarefreeLogMean (σ : ℝ) : ℝ := squarefreeLogMass σ / squarefreeMass σ

/-- The pointed Euler mean is the expectation of `log n` in the state `e_σ`. -/
theorem eulerLogMean_eq_expectation {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ+, ‖eulerPointedState hσ n‖ ^ (2 : ℕ) * Real.log (n : ℝ) = eulerLogMean σ := by
  have hmass := eulerMass_pos hσ
  have hterm : ∀ n : ℕ+, ‖eulerPointedState hσ n‖ ^ (2 : ℕ) * Real.log (n : ℝ)
      = (Real.log (n : ℝ) * (n : ℝ) ^ (-σ)) * (eulerMass σ)⁻¹ := by
    intro n
    have h : ‖eulerPointedState hσ n‖ ^ (2 : ℕ) = (n : ℝ) ^ (-σ) * (eulerMass σ)⁻¹ :=
      norm_eulerStateCoord hσ n
    rw [h]; ring
  rw [tsum_congr hterm, tsum_mul_right, ← eulerLogMass, eulerLogMean, div_eq_mul_inv]

/-- The pointed squarefree mean is the expectation of `log d` in the state `s_σ`. -/
theorem squarefreeLogMean_eq_expectation {σ : ℝ} (hσ : 1 < σ) :
    ∑' d : SquarefreePNat, ‖squarefreePointedState hσ d‖ ^ (2 : ℕ) * Real.log ((d.1 : ℝ))
      = squarefreeLogMean σ := by
  have hmass := squarefreeMass_pos hσ
  have hterm : ∀ d : SquarefreePNat,
      ‖squarefreePointedState hσ d‖ ^ (2 : ℕ) * Real.log ((d.1 : ℝ))
        = (Real.log ((d.1 : ℝ)) * ((d.1 : ℝ)) ^ (-σ)) * (squarefreeMass σ)⁻¹ := by
    intro d
    have h : ‖squarefreePointedState hσ d‖ ^ (2 : ℕ)
        = ((d.1 : ℝ)) ^ (-σ) * (squarefreeMass σ)⁻¹ := norm_squarefreeStateCoord hσ d
    rw [h]; ring
  rw [tsum_congr hterm, tsum_mul_right, ← squarefreeLogMass, squarefreeLogMean, div_eq_mul_inv]

/-! ### Nonnegativity of the four one-sided weights -/

theorem log_rpow_nonneg_pnat {σ : ℝ} (n : ℕ+) : 0 ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-σ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast n.property)
  have hr : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := by positivity
  exact mul_nonneg hlog hr

theorem log_rpow_nonneg_squarefree {σ : ℝ} (d : SquarefreePNat) :
    0 ≤ Real.log ((d.1 : ℝ)) * ((d.1 : ℝ)) ^ (-σ) := log_rpow_nonneg_pnat (σ := σ) d.1

/-- **The unnormalized logarithmic mass split.** -/
theorem eulerLogMass_split {σ : ℝ} (hσ : 1 < σ) :
    eulerLogMass σ
      = squarefreeLogMass σ * eulerMass (2 * σ)
        + 2 * (squarefreeMass σ * eulerLogMass (2 * σ)) := by
  have hσ2 : 1 < 2 * σ := by linarith
  have hA : Summable (fun d : SquarefreePNat => Real.log ((d.1 : ℝ)) * ((d.1 : ℝ)) ^ (-σ)) :=
    summable_squarefree_log_rpow hσ
  have hZ : Summable (fun d : SquarefreePNat => ((d.1 : ℝ)) ^ (-σ)) :=
    summable_squarefree_rpow hσ
  have hE : Summable (fun m : ℕ+ => (m : ℝ) ^ (-(2 * σ))) := summable_pnat_rpow hσ2
  have hB : Summable (fun m : ℕ+ => Real.log (m : ℝ) * (m : ℝ) ^ (-(2 * σ))) :=
    summable_pnat_log_rpow hσ2
  have hB2 : Summable (fun m : ℕ+ => 2 * (Real.log (m : ℝ) * (m : ℝ) ^ (-(2 * σ)))) :=
    hB.mul_left 2
  have hAnn : ∀ d : SquarefreePNat, 0 ≤ Real.log ((d.1 : ℝ)) * ((d.1 : ℝ)) ^ (-σ) :=
    fun d => log_rpow_nonneg_squarefree d
  have hZnn : ∀ d : SquarefreePNat, (0 : ℝ) ≤ ((d.1 : ℝ)) ^ (-σ) := fun d => by positivity
  have hEnn : ∀ m : ℕ+, (0 : ℝ) ≤ (m : ℝ) ^ (-(2 * σ)) := fun m => by positivity
  have hBnn : ∀ m : ℕ+, 0 ≤ Real.log (m : ℝ) * (m : ℝ) ^ (-(2 * σ)) :=
    fun m => log_rpow_nonneg_pnat m
  have hB2nn : ∀ m : ℕ+, 0 ≤ 2 * (Real.log (m : ℝ) * (m : ℝ) ^ (-(2 * σ))) :=
    fun m => by have := hBnn m; linarith
  have hprod1 : Summable (fun q : SquarefreePNat × ℕ+ =>
      (Real.log ((q.1.1 : ℝ)) * ((q.1.1 : ℝ)) ^ (-σ)) * ((q.2 : ℝ)) ^ (-(2 * σ))) :=
    hA.mul_of_nonneg hE (fun d => hAnn d) (fun m => hEnn m)
  have hprod2 : Summable (fun q : SquarefreePNat × ℕ+ =>
      (((q.1.1 : ℝ)) ^ (-σ)) * (2 * (Real.log ((q.2 : ℝ)) * ((q.2 : ℝ)) ^ (-(2 * σ))))) :=
    hZ.mul_of_nonneg hB2 (fun d => hZnn d) (fun m => hB2nn m)
  have hAabs : Summable (fun d : SquarefreePNat => ‖Real.log ((d.1 : ℝ)) * ((d.1 : ℝ)) ^ (-σ)‖) := by
    refine hA.congr fun d => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hAnn d)]
  have hZabs : Summable (fun d : SquarefreePNat => ‖((d.1 : ℝ)) ^ (-σ)‖) := by
    refine hZ.congr fun d => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hZnn d)]
  have hEabs : Summable (fun m : ℕ+ => ‖(m : ℝ) ^ (-(2 * σ))‖) := by
    refine hE.congr fun m => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnn m)]
  have hB2abs : Summable (fun m : ℕ+ => ‖2 * (Real.log (m : ℝ) * (m : ℝ) ^ (-(2 * σ)))‖) := by
    refine hB2.congr fun m => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hB2nn m)]
  have hreindex : eulerLogMass σ
      = ∑' q : SquarefreePNat × ℕ+,
          ((Real.log ((q.1.1 : ℝ)) * ((q.1.1 : ℝ)) ^ (-σ)) * ((q.2 : ℝ)) ^ (-(2 * σ))
            + ((q.1.1 : ℝ)) ^ (-σ)
              * (2 * (Real.log ((q.2 : ℝ)) * ((q.2 : ℝ)) ^ (-(2 * σ))))) := by
    rw [eulerLogMass, ← dyadicSquarefreeSquareEquiv.tsum_eq
      (fun q : SquarefreePNat × ℕ+ =>
        (Real.log ((q.1.1 : ℝ)) * ((q.1.1 : ℝ)) ^ (-σ)) * ((q.2 : ℝ)) ^ (-(2 * σ))
          + ((q.1.1 : ℝ)) ^ (-σ)
            * (2 * (Real.log ((q.2 : ℝ)) * ((q.2 : ℝ)) ^ (-(2 * σ)))))]
    refine tsum_congr fun n => ?_
    have hlog := dyadicSquarefreeSquareEquiv_log n
    have hrp := rpow_eq_squarefree_mul_square (σ := σ) n
    rw [hlog, hrp]
    ring
  rw [hreindex, hprod1.tsum_add hprod2]
  congr 1
  · rw [squarefreeLogMass, eulerMass, tsum_mul_tsum_of_summable_norm hAabs hEabs]
  · have hrw : (2 : ℝ) * (squarefreeMass σ * eulerLogMass (2 * σ))
        = squarefreeMass σ * (2 * eulerLogMass (2 * σ)) := by ring
    rw [hrw, squarefreeMass, eulerLogMass, ← tsum_mul_left,
      tsum_mul_tsum_of_summable_norm hZabs hB2abs]

/-- **Equation (11).**  `b_σ = a_σ + 2 b_{2σ}` — the pointed Hilbert form of the logarithmic
current identity. -/
theorem eulerLogMean_split {σ : ℝ} (hσ : 1 < σ) :
    eulerLogMean σ = squarefreeLogMean σ + 2 * eulerLogMean (2 * σ) := by
  have hσ2 : 1 < 2 * σ := by linarith
  have hZ := squarefreeMass_pos hσ
  have hE2 := eulerMass_pos hσ2
  have hmassEq := squarefreeMass_mul_eulerMass_two_mul hσ
  have hsplit := eulerLogMass_split hσ
  rw [eulerLogMean, eulerLogMean, squarefreeLogMean, hsplit, ← hmassEq]
  field_simp

end RHTower
