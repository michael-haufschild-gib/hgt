import GaloisForLFunctions.HTGeometry.LegendreHalvesField
import GaloisForLFunctions.HTGeometry.MultiquadraticAdjoinDegree
import GaloisForLFunctions.RHTower.XiGlobalKummerAugmentation
import GaloisForLFunctions.RHTower.XiCriticalStripFiniteTensor

/-!
# Finite marked fields of the global Xi Kummer tower

Index `n` carries the label `n + 2`; write `d_n = β_n² ξ`, `F_n = 1 - d_n` and `u_n² = ξ F_n`.
For a finite index set `T` let `L_T = K(u_n : n ∈ T)` inside the algebraic closure `Ω` of the
global meromorphic field `K`; equivalently `L_T = K(q_n : n ∈ T)` with `q_n² = d_n / F_n`.

* `[L_T : K] = 2^|T|`, and `a ∈ K` becomes a square in `L_T` iff `a ∏_{n ∈ U} ξF_n` is a square
  in `K` for some `U ⊆ T`.
* `ξ` and every `F_n` stay nonsquare in `L_T`, while `ξ F_n` is a square for `n ∈ T`; the infinite
  marked field is the directed union of the `L_T`.
* Over every field containing a marking `u_n`, the section `P_n = (d_n, β_n u_n)` of
  `y² = x(x-1)(x-λ_n)`, `λ_n = 1 + d_n`, has a half exactly when `ξ` is a square.  Hence for
  `n ∈ T` the field of halves of `P_n` over `L_T` is the same quadratic extension `L_T(√ξ)`.
-/

noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry WeierstrassCurve.Affine
open scoped IntermediateField

local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective
local instance (priority := high) (F : Type*) [Field F] : DecidableEq F := Classical.decEq F

/-! ## The fields `L_T` -/

/-! `L_T = K(√(ξ F_{n+2}) : n ∈ T)` is `finiteMarkedExtension T`, with
`[L_T : K] = 2^|T|` (`finiteMarkedExtension_finrank`). -/

theorem root_mem_finiteMarkedExtension {T : Finset ℕ} {n : ℕ} (hn : n ∈ T) :
    root n ∈ finiteMarkedExtension T :=
  IntermediateField.subset_adjoin _ _ ⟨n, hn, rfl⟩

private theorem degree_and_twists (T : Finset ℕ) :
    Module.finrank K ↥(IntermediateField.adjoin K (root '' (T : Set ℕ))) = 2 ^ T.card ∧
      ∀ a : K, IsSquare (algebraMap K ↥(IntermediateField.adjoin K (root '' (T : Set ℕ))) a) →
        ∃ U : Finset ℕ, U ⊆ T ∧ IsSquare (a * ∏ n ∈ U, radicand n) :=
  multiquadratic_degree_and_twists radicand root two_ne_zero root_sq
    prod_radicand_not_isSquare T

private theorem radicand_ne_zero' (n : ℕ) : radicand n ≠ 0 := by
  intro h
  apply prod_radicand_not_isSquare {n} (Finset.singleton_nonempty n)
  rw [Finset.prod_singleton, h]
  exact IsSquare.zero

/-- **Finite Kummer kernel.** -/
theorem isSquare_finiteMarkedExtension_iff (T : Finset ℕ) (a : K) :
    IsSquare (algebraMap K (finiteMarkedExtension T) a) ↔
      ∃ U ⊆ T, IsSquare (a * ∏ n ∈ U, radicand n) := by
  refine ⟨(degree_and_twists T).2 a, ?_⟩
  rintro ⟨U, hU, b, hb⟩
  set φ := algebraMap K (finiteMarkedExtension T)
  have hmem : (∏ n ∈ U, root n) ∈ finiteMarkedExtension T :=
    prod_mem (fun n hn => root_mem_finiteMarkedExtension (hU hn))
  set ρ : finiteMarkedExtension T := ⟨_, hmem⟩
  have hρ : ρ * ρ = φ (∏ n ∈ U, radicand n) := by
    apply Subtype.ext
    change (∏ n ∈ U, root n) * (∏ n ∈ U, root n) = algebraMap K Ω (∏ n ∈ U, radicand n)
    rw [← Finset.prod_mul_distrib, map_prod]
    exact Finset.prod_congr rfl (fun n _ => root_sq n)
  have hρ0 : ρ ≠ 0 := by
    intro h0
    rw [h0, zero_mul, eq_comm, map_eq_zero_iff _ φ.injective, Finset.prod_eq_zero_iff] at hρ
    obtain ⟨n, -, hn⟩ := hρ
    exact radicand_ne_zero' n hn
  have hmap := congrArg φ hb
  rw [map_mul, map_mul, ← hρ] at hmap
  refine ⟨φ b / ρ, ?_⟩
  field_simp
  linear_combination hmap

/-- In terms of `q_n² = d_n / F_n` the same field: `L_T = K(q_n : n ∈ T)`. -/
def qRoot (n : ℕ) : Ω :=
  algebraMap K Ω (betaElement n) * root n / algebraMap K Ω (factorElement (n + 2))

theorem qRoot_sq (n : ℕ) : qRoot n * qRoot n =
    algebraMap K Ω (betaElement n ^ 2 * xiElement / factorElement (n + 2)) := by
  have hF : algebraMap K Ω (factorElement (n + 2)) ≠ 0 :=
    (map_ne_zero _).mpr (factorElement_ne_zero (by omega))
  have hu := root_sq n
  rw [radicand, map_mul] at hu
  simp only [qRoot, map_div₀, map_mul, map_pow]
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hF hF) hF]
  linear_combination algebraMap K Ω (betaElement n) ^ 2 *
    algebraMap K Ω (factorElement (n + 2)) * hu

theorem finiteMarkedExtension_eq_adjoin_qRoot (T : Finset ℕ) :
    finiteMarkedExtension T = IntermediateField.adjoin K (qRoot '' (T : Set ℕ)) := by
  apply le_antisymm
  · rw [finiteMarkedExtension, IntermediateField.adjoin_le_iff]
    rintro _ ⟨n, hn, rfl⟩
    have hq : qRoot n ∈ IntermediateField.adjoin K (qRoot '' (T : Set ℕ)) :=
      IntermediateField.subset_adjoin _ _ ⟨n, hn, rfl⟩
    have hβ : algebraMap K Ω (betaElement n) ≠ 0 := (map_ne_zero _).mpr (betaElement_ne_zero n)
    have hF : algebraMap K Ω (factorElement (n + 2)) ≠ 0 :=
      (map_ne_zero _).mpr (factorElement_ne_zero (by omega))
    have he : root n = qRoot n * algebraMap K Ω (factorElement (n + 2)) /
        algebraMap K Ω (betaElement n) := by
      simp only [qRoot]; field_simp
    rw [he]
    exact div_mem (mul_mem hq (IntermediateField.algebraMap_mem _ _))
      (IntermediateField.algebraMap_mem _ _)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨n, hn, rfl⟩
    exact div_mem (mul_mem (IntermediateField.algebraMap_mem _ _)
      (root_mem_finiteMarkedExtension hn)) (IntermediateField.algebraMap_mem _ _)

/-! ## Relation with the infinite marked field -/

theorem finiteMarkedExtension_le_markedExtension (T : Finset ℕ) :
    finiteMarkedExtension T ≤ markedExtension := by
  rw [finiteMarkedExtension, IntermediateField.adjoin_le_iff]
  rintro _ ⟨n, -, rfl⟩
  exact root_mem_markedField n

/-- The infinite marked field is the directed union of the finite marked fields. -/
theorem iSup_finiteMarkedExtension : ⨆ T : Finset ℕ, finiteMarkedExtension T = markedExtension := by
  apply le_antisymm (iSup_le finiteMarkedExtension_le_markedExtension)
  intro z hz
  change z ∈ markedField at hz
  obtain ⟨k, hk⟩ := (Subfield.mem_iSup_of_directed stage_mono.directed_le).mp hz
  have hle : stage k ≤ (finiteMarkedExtension (Finset.range k)).toSubfield := by
    apply Subfield.closure_le.mpr
    rintro w (hw | ⟨n, hn, rfl⟩)
    · obtain ⟨a, rfl⟩ := hw
      exact IntermediateField.algebraMap_mem _ a
    · exact root_mem_finiteMarkedExtension (Finset.mem_range.mpr hn)
  exact (le_iSup finiteMarkedExtension (Finset.range k)) (hle hk)

private theorem isSquare_marked_of_finite {T : Finset ℕ} {a : K}
    (h : IsSquare (algebraMap K (finiteMarkedExtension T) a)) :
    IsSquare (algebraMap K markedExtension a) := by
  obtain ⟨b, hb⟩ := h
  set ι := IntermediateField.inclusion (finiteMarkedExtension_le_markedExtension T)
  refine ⟨ι b, ?_⟩
  rw [← ι.commutes a, hb, map_mul]

theorem xi_not_isSquare_finiteMarkedExtension (T : Finset ℕ) :
    ¬ IsSquare (algebraMap K (finiteMarkedExtension T) xiElement) :=
  fun h => xi_not_isSquare_markedExtension (isSquare_marked_of_finite h)

theorem factor_not_isSquare_finiteMarkedExtension (T : Finset ℕ) (n : ℕ) :
    ¬ IsSquare (algebraMap K (finiteMarkedExtension T) (factorElement (n + 2))) :=
  fun h => factor_not_isSquare_markedExtension n (isSquare_marked_of_finite h)

/-- For `n ∈ T` the classes of `ξ` and `F_n` coincide in `L_T`. -/
theorem radicand_isSquare_finiteMarkedExtension {T : Finset ℕ} {n : ℕ} (hn : n ∈ T) :
    IsSquare (algebraMap K (finiteMarkedExtension T) (xiElement * factorElement (n + 2))) := by
  refine ⟨⟨root n, root_mem_finiteMarkedExtension hn⟩, ?_⟩
  apply Subtype.ext
  exact (root_sq n).symm

/-! ## The original section over any marked field -/

private theorem nonsingular_core {E : Type*} [Field E] [CharZero E] {lam x y b xi' fa u' : E}
    (hl : lam = 1 + b ^ 2 * xi') (hx : x = b ^ 2 * xi') (hy : y = b * u')
    (hbf : b ^ 2 * xi' + fa = 1) (hu : u' * u' = xi' * fa) (hb : b ≠ 0) (hu0 : u' ≠ 0) :
    (LegendreDoubling.curve lam).Nonsingular x y := by
  have hy0 : y ≠ 0 := by rw [hy]; exact mul_ne_zero hb hu0
  apply (nonsingular_iff' x y).mpr
  refine ⟨(equation_iff x y).mpr ?_, Or.inr ?_⟩
  · simp only [LegendreDoubling.curve]
    subst hl hx hy
    linear_combination b ^ 2 * hu + b ^ 2 * xi' * hbf
  · simp only [LegendreDoubling.curve, zero_mul]
    intro h
    have : (2 : E) * y = 0 := by linear_combination h
    exact hy0 ((mul_eq_zero.mp this).resolve_left two_ne_zero)

private theorem half_iff_core {E : Type*} [Field E] [CharZero E] {lam x y b xi' fa u' i' : E}
    (hl : lam = 1 + b ^ 2 * xi') (hx : x = b ^ 2 * xi') (hy : y = b * u')
    (hbf : b ^ 2 * xi' + fa = 1) (hu : u' * u' = xi' * fa) (hi : i' ^ 2 = -1)
    (hb : b ≠ 0) (hxi : xi' ≠ 0) (hfa : fa ≠ 0) (hlam : lam ≠ 0)
    (h : (LegendreDoubling.curve lam).Nonsingular x y) :
    (∃ R : (LegendreDoubling.curve lam).Point, R + R = Point.some x y h) ↔ IsSquare xi' := by
  have hu0 : u' ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hu; exact mul_ne_zero hxi hfa hu.symm
  have hl1 : lam ≠ 1 := by
    intro h1; rw [h1] at hl
    exact mul_ne_zero (pow_ne_zero 2 hb) hxi (by linear_combination -hl)
  have hy0 : y ≠ 0 := by rw [hy]; exact mul_ne_zero hb hu0
  rw [LegendreDoubling.exists_half_iff_square_coordinates hlam hl1 hy0 h]
  have hx1 : x - 1 = -fa := by rw [hx]; linear_combination hbf
  rw [hx1, hx]
  constructor
  · rintro ⟨hs, -⟩
    have h2 := hs.div (IsSquare.sq b)
    rwa [mul_div_cancel_left₀ _ (pow_ne_zero 2 hb)] at h2
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by rintro rfl; exact hxi (by simpa using ha)
    refine ⟨(IsSquare.sq b).mul ⟨a, ha⟩, ⟨i' * u' / a, ?_⟩⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero ha0 ha0)]
    linear_combination (-(u' ^ 2)) * hi + hu + fa * ha

section Marking
variable {F : Type*} [Field F] [Algebra K F]

local instance : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

/-- `λ_n = 1 + d_n`. -/
def lambdaElement (n : ℕ) : K := 1 + betaElement n ^ 2 * xiElement

private theorem lambdaElement_ne_zero (n : ℕ) : lambdaElement n ≠ 0 := by
  have h : lambdaElement n = augmentationElement (n + 2) := by
    rw [augmentationElement_eq_two_sub_factor, lambdaElement, betaElement_sq_mul_xi]; ring
  rw [h]
  intro h0
  exact augmentationElement_not_isSquare (n := n + 2) (by omega) (h0 ▸ IsSquare.zero)

private theorem radicand_ne_zero'' (n : ℕ) : radicand n ≠ 0 := radicand_ne_zero' n

theorem markedPoint_nonsingular (n : ℕ) {u : F} (hu : u * u = algebraMap K F (radicand n)) :
    (LegendreDoubling.curve (algebraMap K F (lambdaElement n))).Nonsingular
      (algebraMap K F (betaElement n ^ 2 * xiElement)) (algebraMap K F (betaElement n) * u) := by
  have hbf := congrArg (algebraMap K F) (betaElement_sq_mul_xi n)
  simp only [map_mul, map_pow, map_sub, map_one] at hbf
  refine nonsingular_core (fa := algebraMap K F (factorElement (n + 2)))
    (xi' := algebraMap K F xiElement) (by simp [lambdaElement]) (by simp) rfl
    (by linear_combination hbf) (by rw [hu, radicand, map_mul])
    ((map_ne_zero _).mpr (betaElement_ne_zero n)) ?_
  intro h0
  rw [h0, zero_mul, eq_comm, map_eq_zero_iff _ (algebraMap K F).injective] at hu
  exact radicand_ne_zero'' n hu

/-- The section `P_n = (d_n, β_n u)` attached to a marking `u² = ξ F_n`. -/
def markedPoint (n : ℕ) {u : F} (hu : u * u = algebraMap K F (radicand n)) :
    (LegendreDoubling.curve (algebraMap K F (lambdaElement n))).Point :=
  .some _ _ (markedPoint_nonsingular n hu)

/-- Over the marked field itself, `P_n` has a half exactly when `ξ` is a square there. -/
theorem markedPoint_has_half_iff (n : ℕ) {u : F} (hu : u * u = algebraMap K F (radicand n)) :
    (∃ R, R + R = markedPoint n hu) ↔ IsSquare (algebraMap K F xiElement) := by
  have hbf := congrArg (algebraMap K F) (betaElement_sq_mul_xi n)
  simp only [map_mul, map_pow, map_sub, map_one] at hbf
  have hI := congrArg (algebraMap K F) (show constPlane Complex.I ^ 2 = -1 by
    rw [← map_pow, Complex.I_sq, map_neg, map_one])
  simp only [map_pow, map_neg, map_one] at hI
  exact half_iff_core (b := algebraMap K F (betaElement n)) (xi' := algebraMap K F xiElement)
    (fa := algebraMap K F (factorElement (n + 2))) (u' := u)
    (i' := algebraMap K F (constPlane Complex.I))
    (by simp [lambdaElement]) (by simp) rfl (by linear_combination hbf)
    (by rw [hu, radicand, map_mul]) hI
    ((map_ne_zero _).mpr (betaElement_ne_zero n)) ((map_ne_zero _).mpr xiElement_ne_zero)
    ((map_ne_zero _).mpr (factorElement_ne_zero (by omega)))
    ((map_ne_zero _).mpr (lambdaElement_ne_zero n)) _

/-- **Halving criterion.**  Over every extension `E` of a marked field, `P_n` has a half exactly
when `ξ` is a square in `E`. -/
theorem markedPoint_halvingDecidedBy (n : ℕ) {u : F} (hu : u * u = algebraMap K F (radicand n))
    {Ω' : Type*} [Field Ω'] [CharZero Ω'] [Algebra F Ω'] :
    LegendreDoubling.HalvingDecidedBy (Ω := Ω') (markedPoint n hu)
      (algebraMap K F xiElement) := by
  intro E
  set σ := algebraMap F E with hσ
  have hbf := congrArg (fun z => σ (algebraMap K F z)) (betaElement_sq_mul_xi n)
  simp only [map_mul, map_pow, map_sub, map_one] at hbf
  have hI := congrArg (fun z => σ (algebraMap K F z)) (show constPlane Complex.I ^ 2 = -1 by
    rw [← map_pow, Complex.I_sq, map_neg, map_one])
  simp only [map_pow, map_neg, map_one] at hI
  have hxi : σ (algebraMap K F xiElement) ≠ 0 := by
    rw [map_ne_zero, map_ne_zero]; exact xiElement_ne_zero
  have hfa : σ (algebraMap K F (factorElement (n + 2))) ≠ 0 := by
    rw [map_ne_zero, map_ne_zero]; exact factorElement_ne_zero (by omega)
  rw [markedPoint, LegendreDoubling.pointMap_some]
  exact half_iff_core (b := σ (algebraMap K F (betaElement n)))
    (xi' := σ (algebraMap K F xiElement)) (fa := σ (algebraMap K F (factorElement (n + 2))))
    (u' := σ u) (i' := σ (algebraMap K F (constPlane Complex.I)))
    (by simp [hσ, lambdaElement]) (by simp [hσ]) (map_mul σ _ _) (by linear_combination hbf)
    (by rw [← map_mul, hu, radicand, map_mul, map_mul]) hI
    (by rw [map_ne_zero, map_ne_zero]; exact betaElement_ne_zero n) hxi hfa
    (by rw [map_ne_zero, map_ne_zero]; exact lambdaElement_ne_zero n) _

end Marking

/-! ## The field of halves over `L_T` -/

/-- A square root of `ξ` in `Ω`. -/
def xiRoot : Ω :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω xiElement) (by decide : 0 < 2))

theorem xiRoot_sq : xiRoot * xiRoot = algebraMap K Ω xiElement := by
  simpa only [xiRoot, pow_two] using
    (Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω xiElement)
      (by decide : 0 < 2)))

theorem finiteMarking_sq (T : Finset ℕ) {n : ℕ} (hn : n ∈ T) :
    (⟨root n, root_mem_finiteMarkedExtension hn⟩ : finiteMarkedExtension T) *
      ⟨root n, root_mem_finiteMarkedExtension hn⟩ =
      algebraMap K (finiteMarkedExtension T) (radicand n) := by
  apply Subtype.ext
  exact root_sq n

/-- The original section `P_n`, `n ∈ T`, over `L_T`. -/
def finiteSection (T : Finset ℕ) {n : ℕ} (hn : n ∈ T) :=
  markedPoint (F := finiteMarkedExtension T) n (finiteMarking_sq T hn)

private theorem xiRoot_sq_finite (T : Finset ℕ) :
    xiRoot * xiRoot = algebraMap (finiteMarkedExtension T) Ω
      (algebraMap K (finiteMarkedExtension T) xiElement) := by
  rw [xiRoot_sq, IsScalarTower.algebraMap_apply K (finiteMarkedExtension T) Ω]

/-- `P_n` is not divisible by two over `L_T`. -/
theorem finiteSection_not_double (T : Finset ℕ) {n : ℕ} (hn : n ∈ T)
    (R : (LegendreDoubling.curve
      (algebraMap K (finiteMarkedExtension T) (lambdaElement n))).Point) :
    R + R ≠ finiteSection T hn := fun hR =>
  xi_not_isSquare_finiteMarkedExtension T ((markedPoint_has_half_iff n _).mp ⟨R, hR⟩)

/-- **Field of halves.**  For `n ∈ T` the coordinates of any half over `Ω` of `P_n` generate
`L_T(√ξ)` over `L_T`; this field is the same for all `n ∈ T`. -/
theorem adjoin_finiteSection_half (T : Finset ℕ) {n : ℕ} (hn : n ∈ T) {x y : Ω}
    {h : (LegendreDoubling.curve (algebraMap (finiteMarkedExtension T) Ω
      (algebraMap K (finiteMarkedExtension T) (lambdaElement n)))).Nonsingular x y}
    (hR : Point.some x y h + Point.some x y h =
      LegendreDoubling.pointMap (algebraMap (finiteMarkedExtension T) Ω) rfl (finiteSection T hn)) :
    IntermediateField.adjoin (finiteMarkedExtension T) ({x, y} : Set Ω) =
      (finiteMarkedExtension T)⟮xiRoot⟯ :=
  LegendreDoubling.adjoin_half_coordinates (xiRoot_sq_finite T)
    (markedPoint_halvingDecidedBy n _) hR

/-- `[L_T(√ξ) : L_T] = 2`. -/
theorem finiteHalvesField_finrank (T : Finset ℕ) :
    Module.finrank (finiteMarkedExtension T) (finiteMarkedExtension T)⟮xiRoot⟯ = 2 :=
  finrank_adjoin_eq_two (xiRoot_sq_finite T)
    (root_not_mem_bot_of_not_isSquare (xiRoot_sq_finite T)
      (xi_not_isSquare_finiteMarkedExtension T))

/-- Each `P_n`, `n ∈ T`, has exactly four halves over `Ω`. -/
theorem finiteSection_ncard_halves (T : Finset ℕ) {n : ℕ} (hn : n ∈ T) :
    {R : (LegendreDoubling.curve (algebraMap (finiteMarkedExtension T) Ω
      (algebraMap K (finiteMarkedExtension T) (lambdaElement n)))).Point |
      R + R = LegendreDoubling.pointMap (algebraMap (finiteMarkedExtension T) Ω) rfl
        (finiteSection T hn)}.ncard = 4 := by
  refine LegendreDoubling.ncard_halves_closure ?_ ?_ (xiRoot_sq_finite T)
    (markedPoint_halvingDecidedBy n _)
  · exact (map_ne_zero _).mpr (lambdaElement_ne_zero n)
  · intro h1
    have h := (algebraMap K (finiteMarkedExtension T)).injective (h1.trans (map_one _).symm)
    rw [lambdaElement] at h
    exact mul_ne_zero (pow_ne_zero 2 (betaElement_ne_zero n)) xiElement_ne_zero
      (by linear_combination h)

end RHTower.XiGlobalKummer
