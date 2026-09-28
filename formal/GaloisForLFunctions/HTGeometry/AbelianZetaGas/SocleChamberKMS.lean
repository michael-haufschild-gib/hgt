import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleChamberLaw
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.KMSState

/-!
# The KMS presentation of the chamber law

On the prime-power mode `(p, j)` put the modified energy `ε_{p,j} = (j + τ/σ) log p`.  On the
chamber
`σ + τ > 1` every mode energy is positive, and at inverse temperature `σ` the KMS occupation ratio
is exactly the gas ratio: `e^{-σ ε_{p,j}} = p^{-jσ-τ}`.  The gas algebra therefore carries a unique
normalized KMS functional for this modified dynamics, and its diagonal restriction is the chamber
law: `P_{σ,τ}(A) = ∏_m ψ(layer_m(A_m))` with layer masses `(1 - q_m) q_m^{A_m}`.  Shifting `τ` by
`u` is the chemical-potential change `ε ↦ ε + (u/σ) log p`, which realizes the fugacity
translation `V_u`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

namespace GasChamber

variable (c : GasChamber)

/-- `(AZC.23)`  The modified mode energy `ε_{p,j} = (j + τ/σ) log p` of the mode `(p, j)`,
`j = n + 1`. -/
def modeEnergy (m : AbelianZetaMode) : ℝ :=
  (((m.2 + 1 : ℕ) : ℝ) + c.tau / c.sigma) * Real.log ((m.1 : ℕ) : ℝ)

/-- `(AZC.23)`  On the chamber every modified mode energy is positive. -/
theorem modeEnergy_pos (m : AbelianZetaMode) : 0 < c.modeEnergy m := by
  have hlog : 0 < Real.log ((m.1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast m.1.prop.one_lt)
  have hj : (1 : ℝ) ≤ ((m.2 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hτσ : 0 < 1 + c.tau / c.sigma := by
    rw [one_add_div c.sigma_pos.ne']
    exact div_pos (by linarith [c.firstDepth]) c.sigma_pos
  exact mul_pos (by linarith) hlog

/-- The gas ratio `p^{-(jσ + τ)}` of the mode `(p, j)`. -/
def modeRatio (m : AbelianZetaMode) : ℝ :=
  ((m.1 : ℕ) : ℝ) ^ (-(((m.2 + 1 : ℕ) : ℝ) * c.sigma + c.tau))

/-- `(AZC.24)`  The KMS occupation ratio at inverse temperature `σ` is the gas ratio:
`e^{-σ ε_{p,j}} = p^{-jσ-τ}`. -/
theorem exp_neg_sigma_modeEnergy (m : AbelianZetaMode) :
    Real.exp (-c.sigma * c.modeEnergy m) = c.modeRatio m := by
  have hp : (0 : ℝ) < ((m.1 : ℕ) : ℝ) := by exact_mod_cast m.1.prop.pos
  rw [modeRatio, Real.rpow_def_of_pos hp, modeEnergy]
  congr 1
  field_simp [c.sigma_pos.ne']

theorem modeRatio_pos (m : AbelianZetaMode) : 0 < c.modeRatio m := by
  rw [← exp_neg_sigma_modeEnergy]
  exact Real.exp_pos _

theorem modeRatio_lt_one (m : AbelianZetaMode) : c.modeRatio m < 1 := by
  rw [← exp_neg_sigma_modeEnergy, Real.exp_lt_one_iff]
  nlinarith [c.modeEnergy_pos m, c.sigma_pos]

/-- The KMS nome `q_m = e^{-σ ε_m}` of the modified dynamics. -/
def modeNome (m : AbelianZetaMode) : ℂ := ((c.modeRatio m : ℝ) : ℂ)

theorem modeNome_ne_zero (m : AbelianZetaMode) : c.modeNome m ≠ 0 := by
  rw [modeNome, ne_eq, Complex.ofReal_eq_zero]
  exact (c.modeRatio_pos m).ne'

theorem norm_modeNome_lt_one (m : AbelianZetaMode) : ‖c.modeNome m‖ < 1 := by
  rw [modeNome, Complex.norm_real, Real.norm_of_nonneg (c.modeRatio_pos m).le]
  exact c.modeRatio_lt_one m

/-- The imaginary-time modular flow of the modified dynamics. -/
def modularTwist : GasAlgebra AbelianZetaMode →ₐ[ℂ] GasAlgebra AbelianZetaMode :=
  twist c.modeNome c.modeNome_ne_zero

/-- The KMS state of the modified dynamics. -/
def kmsState : GasAlgebra AbelianZetaMode →ₗ[ℂ] ℂ := gibbs c.modeNome

/-- **Unique KMS state.**  The gas algebra carries exactly one normalized functional satisfying the
KMS exchange identity for the modified dynamics. -/
theorem kms_existsUnique :
    ∃! ψ : GasAlgebra AbelianZetaMode →ₗ[ℂ] ℂ,
      (∀ a b : GasAlgebra AbelianZetaMode, ψ (a * b) = ψ (b * c.modularTwist a)) ∧ ψ 1 = 1 := by
  refine ⟨c.kmsState, ⟨gibbs_exchange c.modeNome c.modeNome_ne_zero, gibbs_one c.modeNome⟩, ?_⟩
  rintro ψ ⟨hexch, hone⟩
  exact gas_kms_unique ψ c.modeNome c.modeNome_ne_zero c.norm_modeNome_lt_one hexch hone

/-- Each occupation layer carries the geometric mass `(1 - q_m) q_m^n`. -/
theorem kmsState_layer (m : AbelianZetaMode) (n : ℕ) :
    c.kmsState ((gasV m) ^ n * (1 - gasV m * gasW m) * (gasW m) ^ n) =
      (1 - c.modeNome m) * c.modeNome m ^ n :=
  kms_layer_mass c.kmsState c.modularTwist (gibbs_exchange c.modeNome c.modeNome_ne_zero)
    (twist_gasV c.modeNome c.modeNome_ne_zero m) (gasW_mul_gasV m) (gibbs_one c.modeNome) n

theorem one_sub_modeNome (m : AbelianZetaMode) :
    1 - c.modeNome m = modeEulerFactor c.sigma c.tau m := by
  rw [modeNome, modeRatio, modeEulerFactor,
    Complex.ofReal_cpow (by exact_mod_cast m.1.prop.pos.le)]
  push_cast
  rfl

/-- The Gibbs weight is the product of the mode ratios over the occupations. -/
theorem weight_eq_prod (A : AbelianZetaGroupClass) :
    c.weight A = ∏ m ∈ A.support, c.modeRatio m ^ (A m) := by
  classical
  simp only [weight, AbelianZetaGroupClass.order, AbelianZetaGroupClass.socleOrder, Finsupp.prod,
    Nat.cast_prod, Nat.cast_pow]
  rw [← Real.finsetProd_rpow A.support
    (fun m => ((m.1 : ℝ) ^ (AbelianZetaMode.depth m * A m)))
    (fun m _ => pow_nonneg (by positivity) _) (-c.sigma)]
  rw [← Real.finsetProd_rpow A.support
    (fun m => ((m.1 : ℝ) ^ (A m)))
    (fun m _ => pow_nonneg (by positivity) _) (-c.tau)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m _
  have hp : 0 < ((m.1 : ℕ) : ℝ) := by exact_mod_cast m.1.prop.pos
  rw [modeRatio, ← Real.rpow_mul_natCast hp.le,
    ← Real.rpow_natCast (((m.1 : ℕ) : ℝ)) (AbelianZetaMode.depth m * A m),
    ← Real.rpow_natCast (((m.1 : ℕ) : ℝ)) (A m), ← Real.rpow_mul hp.le, ← Real.rpow_mul hp.le,
    ← Real.rpow_add hp]
  congr 1
  simp only [AbelianZetaMode.depth]
  push_cast
  ring

/-- `(AZC.24)`  **Diagonal restriction of the KMS state.**  The chamber law is the product of the
KMS layer masses: `P_{σ,τ}(A) = ∏_m ψ(layer_m(A_m)) = ∏_m (1 - q_m) q_m^{A_m}`. -/
theorem law_singleton_eq_tprod_kmsLayer (A : AbelianZetaGroupClass) :
    (((c.law {A}).toReal : ℝ) : ℂ) =
      ∏' m, c.kmsState ((gasV m) ^ (A m) * (1 - gasV m * gasW m) * (gasW m) ^ (A m)) := by
  classical
  simp_rw [kmsState_layer, one_sub_modeNome]
  have h1 := hasProd_modeEulerFactor c.sigma_pos (v := (c.tau : ℂ))
    (by simpa using c.firstDepth)
  have h2 : Multipliable fun m : AbelianZetaMode => c.modeNome m ^ (A m) := by
    refine multipliable_of_hasFiniteMulSupport (A.support.finite_toSet.subset fun m hm => ?_)
    by_contra hnot
    have hAm : A m = 0 := by simpa using hnot
    exact hm (by simp [hAm])
  rw [h1.multipliable.tprod_mul h2, h1.tprod_eq]
  have hfin : ∏' m, c.modeNome m ^ (A m) = ∏ m ∈ A.support, c.modeNome m ^ (A m) := by
    refine tprod_eq_prod fun m hm => ?_
    have hAm : A m = 0 := by simpa using hm
    simp [hAm]
  rw [hfin]
  have hw : ((c.weight A : ℝ) : ℂ) = ∏ m ∈ A.support, c.modeNome m ^ (A m) := by
    rw [weight_eq_prod]
    push_cast
    rfl
  have hL : socleLadder c.sigma (c.tau : ℂ) ≠ 0 :=
    socleLadder_ne_zero_of_mem c.sigma_pos
      (by simp only [socleChamber, Set.mem_setOf_eq, Complex.ofReal_re]; linarith [c.firstDepth])
  rw [← hw, ← c.ofReal_toReal_law_mul_socleLadder A]
  field_simp

/-- Fugacity translation `V_u` is the chemical-potential change `ε ↦ ε + (u/σ) log p`. -/
theorem modeEnergy_translate (u : ℝ) (hu : 1 < c.sigma + c.tau + u) (m : AbelianZetaMode) :
    (c.translate u hu).modeEnergy m = c.modeEnergy m + u / c.sigma * Real.log ((m.1 : ℕ) : ℝ) := by
  simp only [modeEnergy, translate]
  field_simp [c.sigma_pos.ne']
  ring

end GasChamber

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
