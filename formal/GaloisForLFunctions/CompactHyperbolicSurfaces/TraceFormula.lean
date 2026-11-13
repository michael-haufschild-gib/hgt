import GaloisForLFunctions.CompactHyperbolicSurfaces.ClassOrbitalIntegrals
import GaloisForLFunctions.CompactHyperbolicSurfaces.DiffKernelDiagonal
import GaloisForLFunctions.CompactHyperbolicSurfaces.MercerTrace

/-!
# The trace formula for `T_a − T_b`

For a compact quotient whose nontrivial elements are hyperbolic and `1 < a < b`:

  `Σ_j ν_j = |F| D_{a,b}(0) + Σ_{[γ] ≠ 1} ℓ₀([γ]) g_{a,b}(ℓ([γ]))`  (`trace_formula`),

with `g_{a,b}(ℓ) = (e^{−(a−½)ℓ}/(2a−1) − e^{−(b−½)ℓ}/(2b−1))/(2 sinh(ℓ/2))` (`geomWeight`).  The
identity term is `Σ_F D(u(z,z)) = |F| D(0)`; the rest is grouped by conjugacy classes
(`tsum_isConj_lintegral`), and the orbital integral is the Abel transform
`𝒜D(ℓ) = e^{−(a−½)ℓ}/(2a−1) − e^{−(b−½)ℓ}/(2b−1)` divided by `2 sinh(ℓ/2)` (`lintegral_orbit_diffProfile`).
-/

open MeasureTheory Set UpperHalfPlane Real
open scoped MatrixGroups ENNReal Pointwise

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry RHTower

noncomputable section

/-- The geometric weight of a class of length `ℓ`. -/
def geomWeight (a b ℓ : ℝ) : ℝ :=
  (exp (-((a - 1 / 2) * ℓ)) / (2 * a - 1) - exp (-((b - 1 / 2) * ℓ)) / (2 * b - 1)) /
    (2 * sinh (ℓ / 2))

theorem geomWeight_nonneg {a b ℓ : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b) (hℓ : 0 < ℓ) :
    0 ≤ geomWeight a b ℓ := by
  have hs : 0 < sinh (ℓ / 2) := Real.sinh_pos_iff.mpr (by linarith)
  refine div_nonneg ?_ (by positivity)
  have h1 : exp (-((b - 1 / 2) * ℓ)) ≤ exp (-((a - 1 / 2) * ℓ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : 1 / (2 * b - 1) ≤ 1 / (2 * a - 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h3 : exp (-((b - 1 / 2) * ℓ)) / (2 * b - 1) ≤ exp (-((a - 1 / 2) * ℓ)) / (2 * a - 1) := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    exact mul_le_mul h1 h2 (by have : (0:ℝ) < 2 * b - 1 := by linarith; positivity)
      (exp_pos _).le
  linarith

theorem sinh_sq_half_eq {ℓ : ℝ} : sinh (ℓ / 2) ^ 2 = (exp ℓ - 1) ^ 2 / (4 * exp ℓ) := by
  have h : exp ℓ = exp (ℓ / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have hp : 0 < exp (ℓ / 2) := exp_pos _
  rw [Real.sinh_eq, h, Real.exp_neg]
  field_simp
  ring

/-- **The orbital weight.**  `∫_ℝ D((N − 1)²/(4N)·(1 + t²)) dt = g_{a,b}(ℓ)` for `N = e^ℓ`. -/
theorem lintegral_orbit_diffProfile {a b ℓ : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b) (hℓ : 0 < ℓ) :
    ∫⁻ t : ℝ, diffProfile a b ((exp ℓ - 1) ^ 2 / (4 * exp ℓ) * (1 + t ^ 2)) =
      ENNReal.ofReal (geomWeight a b ℓ) := by
  have hs : 0 < sinh (ℓ / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have habel := abelL_diffKernel ha hab ℓ
  rw [abelL, lintegral_eq_ofReal_mul_lintegral_comp_mul _ (by positivity : 0 < 2 * sinh (ℓ / 2))]
    at habel
  have hint : ∫⁻ t : ℝ, diffProfile a b ((exp ℓ - 1) ^ 2 / (4 * exp ℓ) * (1 + t ^ 2)) =
      ∫⁻ η : ℝ, ENNReal.ofReal (diffKernel a b ((2 * sinh (ℓ / 2) * η) ^ 2 / 4 +
        sinh (ℓ / 2) ^ 2)) := by
    refine lintegral_congr fun t => ?_
    rw [diffProfile, ← sinh_sq_half_eq]
    congr 2
    ring
  rw [hint, geomWeight, abs_of_pos hℓ] at *
  rw [ENNReal.ofReal_div_of_pos (by positivity), ← habel, mul_comm,
    ENNReal.mul_div_cancel_right (by simp [hs]) ENNReal.ofReal_ne_top]

namespace CompactQuotient

variable (X : CompactQuotient)

/-- A representative of a conjugacy class. -/
def classRep (c : ConjClasses X.Γ) : X.Γ := c.exists_rep.choose

theorem mk_classRep (c : ConjClasses X.Γ) : ConjClasses.mk (X.classRep c) = c :=
  c.exists_rep.choose_spec

/-- The length of a class. -/
def classLen (c : ConjClasses X.Γ) : ℝ := hypLen ((X.classRep c : X.Γ) : SL(2, ℝ))

/-- The primitive length of a class. -/
def classPrimLen (c : ConjClasses X.Γ) : ℝ := primLen (X.classRep c)

theorem classRep_ne_one {c : ConjClasses X.Γ} (hc : c ≠ 1) : X.classRep c ≠ 1 := by
  intro h
  apply hc
  rw [← X.mk_classRep c, h]
  rfl

variable {X} (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|)
include hhyp

theorem classLen_pos {c : ConjClasses X.Γ} (hc : c ≠ 1) : 0 < X.classLen c := by
  have h := hhyp _ (X.classRep_ne_one hc)
  unfold classLen hypLen
  have : 1 < |trSL ((X.classRep c : X.Γ) : SL(2, ℝ))| / 2 := by linarith
  have := Real.arcosh_pos this
  linarith

theorem classPrimLen_pos {c : ConjClasses X.Γ} (hc : c ≠ 1) : 0 < X.classPrimLen c := by
  obtain ⟨σ, γ₀, ℓ₀, m, hℓ₀, hm, hγm, hC, hf⟩ :=
    exists_primitive_root X.cocompactFree hhyp _ (X.classRep_ne_one hc)
  unfold classPrimLen
  rw [primLen_eq hℓ₀ hC hf]
  exact hℓ₀

/-- **The trace formula, in `[0, ∞]`.** -/
theorem lintegral_autK_diag {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    ∫⁻ z in X.F, autK X.Γ (diffProfile a b) z z =
      volume X.F * ENNReal.ofReal (diffKernel a b 0) +
        ∑' c : {c : ConjClasses X.Γ // c ≠ 1},
          ENNReal.ofReal (X.classPrimLen c) * ENNReal.ofReal (geomWeight a b (X.classLen c)) := by
  haveI := X.cocompactFree.countable
  have ha' : 1 / 2 < a := by linarith
  have hmeasD : Measurable (diffProfile a b) := measurable_diffProfile (by linarith) hab
  set f : X.Γ → ℍ → ℝ≥0∞ := fun γ z => diffProfile a b (pairU z (((γ : X.Γ) : SL(2, ℝ)) • z))
  have hfm : ∀ γ, Measurable (f γ) := fun γ =>
    hmeasD.comp ((continuous_pairU.comp (continuous_id.prodMk (continuous_const_smul _))).measurable)
  have hsplit : ∀ z, autK X.Γ (diffProfile a b) z z =
      diffProfile a b 0 + ∑' γ : X.Γ, ite (γ = 1) 0 (f γ z) := by
    intro z
    rw [autK, ENNReal.tsum_eq_add_tsum_ite (1 : X.Γ)]
    congr 1
    simp only [OneMemClass.coe_one, one_smul, pairU, dist_self]
    norm_num
  simp_rw [hsplit]
  rw [lintegral_add_left measurable_const, setLIntegral_const, mul_comm,
    lintegral_tsum fun γ => by
      by_cases h : γ = 1
      · simp only [h, ite_true]; exact measurable_const.aemeasurable
      · simp only [h, ite_false]; exact (hfm γ).aemeasurable]
  congr 1
  have hite : ∀ γ : X.Γ, ∫⁻ z in X.F, ite (γ = 1) 0 (f γ z) =
      ite (γ = 1) 0 (∫⁻ z in X.F, f γ z) := by
    intro γ; by_cases h : γ = 1 <;> simp [h]
  simp_rw [hite]
  -- regroup by conjugacy classes
  rw [← (Equiv.sigmaFiberEquiv (ConjClasses.mk : X.Γ → ConjClasses X.Γ)).tsum_eq,
    ENNReal.tsum_sigma', ENNReal.tsum_eq_add_tsum_ite (1 : ConjClasses X.Γ)]
  have h1 : ∑' γ : {γ : X.Γ // ConjClasses.mk γ = 1},
      ite ((Equiv.sigmaFiberEquiv ConjClasses.mk ⟨1, γ⟩ : X.Γ) = 1) 0
        (∫⁻ z in X.F, f (Equiv.sigmaFiberEquiv ConjClasses.mk ⟨1, γ⟩) z) = 0 := by
    refine ENNReal.tsum_eq_zero.mpr fun γ => ?_
    have : (γ : X.Γ) = 1 := by
      have := γ.2
      rw [← ConjClasses.mk_one, ConjClasses.mk_eq_mk_iff_isConj] at this
      exact isConj_one_right.mp this.symm
    simp [Equiv.sigmaFiberEquiv_apply, this]
  rw [h1, zero_add, ← tsum_subtype_eq_of_support_subset (s := {c | c ≠ 1})]
  swap
  · intro c hc
    by_contra h
    simp only [mem_setOf_eq, not_not] at h
    simp [h] at hc
  refine tsum_congr fun c => ?_
  have hc : (c : ConjClasses X.Γ) ≠ 1 := c.2
  rw [if_neg hc]
  have hne : ∀ γ : {γ : X.Γ // ConjClasses.mk γ = c}, (γ : X.Γ) ≠ 1 := by
    intro γ h
    apply hc
    rw [← γ.2, h]
    rfl
  simp only [Equiv.sigmaFiberEquiv_apply]
  simp_rw [fun γ : {γ : X.Γ // ConjClasses.mk γ = c} => if_neg (hne γ)]
  -- the fibre of `c` is the conjugacy class of its representative
  let e : {γ : X.Γ // IsConj (X.classRep c) γ} ≃ {γ : X.Γ // ConjClasses.mk γ = c} :=
    Equiv.subtypeEquivRight fun γ => by
      rw [← ConjClasses.mk_eq_mk_iff_isConj, X.mk_classRep, eq_comm]
  rw [← e.tsum_eq]
  simp only [e, Equiv.subtypeEquivRight_apply_coe]
  rw [tsum_isConj_lintegral X hhyp _ (X.classRep_ne_one hc) hmeasD,
    lintegral_orbit_diffProfile ha' hab.le (X.classLen_pos hhyp hc)]
  rfl

/-- **The trace formula.**  `Σ_j ν_j = |F| D(0) + Σ_{[γ] ≠ 1} ℓ₀ g_{a,b}(ℓ)`, the class series
converging. -/
theorem trace_formula {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    Summable (fun c : {c : ConjClasses X.Γ // c ≠ 1} =>
        X.classPrimLen c * geomWeight a b (X.classLen c)) ∧
      ∑' j, X.nu ha (b := b) j = (volume X.F).toReal * diffKernel a b 0 +
        ∑' c : {c : ConjClasses X.Γ // c ≠ 1},
          X.classPrimLen c * geomWeight a b (X.classLen c) := by
  have ha' : 1 / 2 < a := by linarith
  have hnn : ∀ c : {c : ConjClasses X.Γ // c ≠ 1},
      0 ≤ X.classPrimLen c * geomWeight a b (X.classLen c) := fun c =>
    mul_nonneg (X.classPrimLen_pos hhyp c.2).le
      (geomWeight_nonneg ha' hab.le (X.classLen_pos hhyp c.2))
  have hofReal : ∀ c : {c : ConjClasses X.Γ // c ≠ 1},
      ENNReal.ofReal (X.classPrimLen c) * ENNReal.ofReal (geomWeight a b (X.classLen c)) =
        ENNReal.ofReal (X.classPrimLen c * geomWeight a b (X.classLen c)) := fun c =>
    (ENNReal.ofReal_mul (X.classPrimLen_pos hhyp c.2).le).symm
  have hL := X.lintegral_autK_diag hhyp ha hab
  simp_rw [hofReal] at hL
  -- the left side is finite
  obtain ⟨B, -, hB⟩ := X.exists_diffKer_le ha hab
  have hfin : ∫⁻ z in X.F, autK X.Γ (diffProfile a b) z z < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) (?_ : ∫⁻ _ in X.F, ENNReal.ofReal B < ∞)
    · rw [X.autK_diffProfile_eq ha hab]; exact ENNReal.ofReal_le_ofReal (hB z z)
    · rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top X.volume_F_lt_top
  have hclass_fin : ∑' c : {c : ConjClasses X.Γ // c ≠ 1},
      ENNReal.ofReal (X.classPrimLen c * geomWeight a b (X.classLen c)) ≠ ∞ := by
    intro h
    rw [hL, h, add_top] at hfin
    exact lt_irrefl _ hfin
  have hsum : Summable (fun c : {c : ConjClasses X.Γ // c ≠ 1} =>
      X.classPrimLen c * geomWeight a b (X.classLen c)) := by
    have := ENNReal.summable_toReal hclass_fin
    exact this.congr fun c => ENNReal.toReal_ofReal (hnn c)
  refine ⟨hsum, ?_⟩
  rw [(X.hasSum_nu ha hab).tsum_eq,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => X.diffKer_nonneg hab z z)
      (X.continuous_diffKer_diag ha hab).aestronglyMeasurable]
  have hcongr : ∫⁻ z in X.F, ENNReal.ofReal (X.diffKer a b z z) =
      ∫⁻ z in X.F, autK X.Γ (diffProfile a b) z z :=
    lintegral_congr fun z => (X.autK_diffProfile_eq ha hab z z).symm
  rw [hcongr, hL, ENNReal.toReal_add (ENNReal.mul_ne_top X.volume_F_lt_top.ne
      ENNReal.ofReal_ne_top) hclass_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (diffKernel_nonneg ha' hab.le 0),
    ENNReal.tsum_toReal_eq fun _ => ENNReal.ofReal_ne_top]
  congr 1
  exact tsum_congr fun c => ENNReal.toReal_ofReal (hnn c)

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
