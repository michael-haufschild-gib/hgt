import GaloisForLFunctions.RHTower.MellinIteratedDerivative
import GaloisForLFunctions.RHTower.FriableMomentZetaJet
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume
import GaloisForLFunctions.RHTower.ThetaHalfPlaneBound

/-!
# The friable density and its Mellin transform

The friable measure `dμ_S = Σ_{n S-smooth} e^{-nx} dx` has Mellin transform `Γ(s) ζ_S(s)` on the
half-plane `0 < Re s`, and its density decays faster than every power at infinity while staying
smaller than every negative power at the origin.
-/

open Filter MeasureTheory Set Asymptotics GaloisForLFunctions

open scoped Topology

namespace RHTower

noncomputable section

variable {k : ℕ}

/-- The `S`-smooth integer with exponent vector `ν`. -/
def smoothNat (p : Fin k → ℕ) (ν : Fin k →₀ ℕ) : ℕ := ∏ i, (p i) ^ (ν i)

theorem one_le_smoothNat {p : Fin k → ℕ} (hp : ∀ i, 1 ≤ p i) (ν : Fin k →₀ ℕ) :
    1 ≤ smoothNat p ν :=
  Finset.one_le_prod' fun i _ => Nat.one_le_pow _ _ (by have := hp i; omega)

theorem smoothNat_pos {p : Fin k → ℕ} (hp : ∀ i, 1 ≤ p i) (ν : Fin k →₀ ℕ) :
    0 < smoothNat p ν := one_le_smoothNat hp ν

/-- The friable Dirichlet monomial `n_ν^{-σ}` is the nome monomial of the local weights. -/
theorem smoothNat_rpow_eq_nomeMonomial {p : Fin k → ℕ} (hp : ∀ i, 1 ≤ p i) (σ : ℝ)
    (ν : Fin k →₀ ℕ) :
    ((smoothNat p ν : ℝ)) ^ (-σ) = ∏ i, ((p i : ℝ) ^ (-σ)) ^ (ν i) := by
  have hpos : ∀ i, (0 : ℝ) < (p i : ℝ) := fun i => by
    have := hp i
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  rw [smoothNat]
  push_cast
  rw [← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast ((p i : ℝ)) (ν i), ← Real.rpow_mul (hpos i).le,
    ← Real.rpow_natCast (((p i : ℝ)) ^ (-σ)) (ν i), ← Real.rpow_mul (hpos i).le]
  congr 1
  ring

theorem summable_smoothNat_rpow {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) {σ : ℝ} (hσ : 0 < σ) :
    Summable fun ν : Fin k →₀ ℕ => ((smoothNat p ν : ℝ)) ^ (-σ) := by
  have hp1 : ∀ i, 1 ≤ p i := fun i => by have := hp i; omega
  set u : Fin k → ℂ := fun i => ((((p i : ℝ)) ^ (-σ) : ℝ) : ℂ) with hu
  have hulty : ∀ i, ‖u i‖ < 1 := by
    intro i
    have hpi : (1 : ℝ) < (p i : ℝ) := by
      have := hp i
      exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two this
    have hlt : ((p i : ℝ)) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hpi (by linarith)
    have hnn : (0 : ℝ) ≤ ((p i : ℝ)) ^ (-σ) := Real.rpow_nonneg (by positivity) _
    rw [hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hlt
  have hsum : Summable fun ν : Fin k →₀ ℕ => ‖HTGeometry.nomeMonomial u ν‖ := by
    have h := (HTGeometry.summable_nomeMonomial_pow_iff 0 u hulty).2 (Summable.of_finite)
    simpa using h
  refine hsum.of_nonneg_of_le (fun ν => Real.rpow_nonneg (by positivity) _) (fun ν => ?_)
  rw [smoothNat_rpow_eq_nomeMonomial hp1 σ ν, HTGeometry.nomeMonomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hval : ‖∏ i, u i ^ ν i‖ = ∏ i, ((p i : ℝ) ^ (-σ)) ^ (ν i) := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_pow]
    congr 1
    have hui : u i = (((p i : ℝ) ^ (-σ) : ℝ) : ℂ) := rfl
    rw [hui, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  rw [hval]

/-! ## The exponential majorant -/

/-- Every negative real power dominates the decaying exponential. -/
theorem exp_neg_le_rpow_neg {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → Real.exp (-u) ≤ C * u ^ (-σ) := by
  set m : ℕ := ⌈σ⌉₊ with hm
  refine ⟨1 + (m.factorial : ℝ), by positivity, fun u hu => ?_⟩
  have hexp : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hupow : u ^ σ ≤ 1 + (m.factorial : ℝ) * Real.exp u := by
    rcases le_or_gt u 1 with h1 | h1
    · have : u ^ σ ≤ 1 := Real.rpow_le_one hu.le h1 hσ.le
      nlinarith [Real.exp_pos u, Nat.factorial_pos m,
        (show (0 : ℝ) ≤ (m.factorial : ℝ) by positivity)]
    · have hσm : σ ≤ (m : ℝ) := Nat.le_ceil σ
      have h2 : u ^ σ ≤ u ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le hσm
      rw [Real.rpow_natCast] at h2
      have h3 := pow_le_factorial_mul_exp hu.le m
      linarith
  have hupos : (0 : ℝ) < u ^ σ := Real.rpow_pos_of_pos hu σ
  have hkey : Real.exp (-u) * u ^ σ ≤ 1 + (m.factorial : ℝ) := by
    rw [Real.exp_neg]
    have hle : u ^ σ ≤ (1 + (m.factorial : ℝ)) * Real.exp u := by
      nlinarith [Real.one_le_exp hu.le]
    rw [inv_mul_eq_div, div_le_iff₀ hexp]
    linarith
  have hrpow : u ^ (-σ) = (u ^ σ)⁻¹ := by
    rw [Real.rpow_neg hu.le]
  rw [hrpow, ← div_eq_mul_inv, le_div_iff₀ hupos]
  linarith

/-! ## The friable density -/

/-- The friable density `Σ_{n S-smooth} e^{-nx}`. -/
def friableDensity (p : Fin k → ℕ) (x : ℝ) : ℂ :=
  ∑' ν : Fin k →₀ ℕ, ((Real.exp (-((smoothNat p ν : ℝ) * x)) : ℝ) : ℂ)

theorem summable_friableTerm {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) {x : ℝ} (hx : 0 < x) :
    Summable fun ν : Fin k →₀ ℕ => Real.exp (-((smoothNat p ν : ℝ) * x)) := by
  obtain ⟨C, hC0, hC⟩ := exp_neg_le_rpow_neg (σ := 1) one_pos
  have hp1 : ∀ i, 1 ≤ p i := fun i => by have := hp i; omega
  have hmaj : Summable fun ν : Fin k →₀ ℕ =>
      C * x ^ (-(1 : ℝ)) * ((smoothNat p ν : ℝ)) ^ (-(1 : ℝ)) :=
    ((summable_smoothNat_rpow hp one_pos).mul_left _)
  refine hmaj.of_nonneg_of_le (fun ν => (Real.exp_pos _).le) (fun ν => ?_)
  have hn : (0 : ℝ) < (smoothNat p ν : ℝ) := by
    exact_mod_cast smoothNat_pos hp1 ν
  have hnx : (0 : ℝ) < (smoothNat p ν : ℝ) * x := mul_pos hn hx
  have h := hC _ hnx
  refine h.trans (le_of_eq ?_)
  rw [Real.mul_rpow hn.le hx.le]
  ring

/-- The friable Dirichlet value `ζ_S(σ) = Σ_ν n_ν^{-σ}`. -/
def friableDirichlet (p : Fin k → ℕ) (σ : ℝ) : ℝ :=
  ∑' ν : Fin k →₀ ℕ, ((smoothNat p ν : ℝ)) ^ (-σ)

theorem friableDirichlet_nonneg (p : Fin k → ℕ) (σ : ℝ) : 0 ≤ friableDirichlet p σ :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **The global majorant of the friable density.** -/
theorem norm_friableDensity_le {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) {σ : ℝ} (hσ : 0 < σ)
    {C : ℝ} (hC : ∀ u : ℝ, 0 < u → Real.exp (-u) ≤ C * u ^ (-σ)) {x : ℝ} (hx : 0 < x) :
    ‖friableDensity p x‖ ≤ C * friableDirichlet p σ * x ^ (-σ) := by
  have hp1 : ∀ i, 1 ≤ p i := fun i => by have := hp i; omega
  have hsum := summable_friableTerm hp hx
  have hnorm : ∀ ν : Fin k →₀ ℕ,
      ‖((Real.exp (-((smoothNat p ν : ℝ) * x)) : ℝ) : ℂ)‖
        = Real.exp (-((smoothNat p ν : ℝ) * x)) := by
    intro ν
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hsummableNorm : Summable fun ν : Fin k →₀ ℕ =>
      ‖((Real.exp (-((smoothNat p ν : ℝ) * x)) : ℝ) : ℂ)‖ := by
    refine hsum.congr fun ν => (hnorm ν).symm
  have hbound := norm_tsum_le_tsum_norm hsummableNorm
  refine hbound.trans ?_
  have hmaj : Summable fun ν : Fin k →₀ ℕ =>
      C * x ^ (-σ) * ((smoothNat p ν : ℝ)) ^ (-σ) :=
    (summable_smoothNat_rpow hp hσ).mul_left _
  have hterm : ∀ ν : Fin k →₀ ℕ,
      ‖((Real.exp (-((smoothNat p ν : ℝ) * x)) : ℝ) : ℂ)‖
        ≤ C * x ^ (-σ) * ((smoothNat p ν : ℝ)) ^ (-σ) := by
    intro ν
    rw [hnorm ν]
    have hn : (0 : ℝ) < (smoothNat p ν : ℝ) := by exact_mod_cast smoothNat_pos hp1 ν
    have h := hC _ (mul_pos hn hx)
    refine h.trans (le_of_eq ?_)
    rw [Real.mul_rpow hn.le hx.le]
    ring
  refine (Summable.tsum_le_tsum hterm hsummableNorm hmaj).trans (le_of_eq ?_)
  rw [tsum_mul_left, friableDirichlet]
  ring

theorem continuousOn_friableDensity {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (friableDensity p) (Ioi a) := by
  have hp1 : ∀ i, 1 ≤ p i := fun i => by have := hp i; omega
  refine continuousOn_tsum (fun ν => ?_) (summable_friableTerm hp ha) (fun ν x hx => ?_)
  · exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)).continuousOn
  · have hxa : a < x := hx
    have hn : (0 : ℝ) < (smoothNat p ν : ℝ) := by exact_mod_cast smoothNat_pos hp1 ν
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    nlinarith

theorem continuousOn_friableDensity_Ioi_zero {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) :
    ContinuousOn (friableDensity p) (Ioi (0 : ℝ)) := by
  refine continuousOn_of_forall_continuousAt fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  refine (continuousOn_friableDensity hp (by linarith : (0 : ℝ) < x / 2)).continuousAt ?_
  exact isOpen_Ioi.mem_nhds (by simp only [mem_Ioi]; linarith)

theorem locallyIntegrableOn_friableDensity {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) :
    LocallyIntegrableOn (friableDensity p) (Ioi (0 : ℝ)) :=
  (continuousOn_friableDensity_Ioi_zero hp).locallyIntegrableOn measurableSet_Ioi

end

end RHTower
