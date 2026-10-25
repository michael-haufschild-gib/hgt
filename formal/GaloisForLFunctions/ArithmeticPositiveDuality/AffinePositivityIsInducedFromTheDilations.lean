import GaloisForLFunctions.ArithmeticPositiveDuality.TheTwoPrimeSplineOrbitIsABochnerProblemOnTheTorus
import GaloisForLFunctions.ArithmeticPositiveDuality.WeilsTheoremForCurvesIsPositiveDefinitenessOnZ
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Affine positivity is induced from the dilations

The affine group `x ↦ ax + b` of `ℚ` carries both ring operations: dilations `x ↦ rx` and the
successor `x ↦ x + 1`, which do not commute. A positivity principle on it is a positive-definite
function `φ` on the group, `Σ c̄_a φ(x_a⁻¹ x_b) c_b ≥ 0`. The question is whether such a principle,
restricted to the dilations, can carry more than quadratic positivity of the Weil form.

**Restriction–induction law** (`exists_isPosDefOnGroup_extension_iff`). For a subgroup `H` of any
group `G`, a function `ψ` on `H` is the restriction of a positive-definite function on `G` iff `ψ`
is positive definite on `H`. Restriction is immediate; for the converse the extension by zero is
positive definite (`isPosDefOnGroup_extendFromSubgroup`): writing `x = r(x) h(x)` with a
left-coset representative `r(x)`, the Gram form splits into one Gram form of `ψ` per coset.

**For `ζ`** (`riemannHypothesis_iff_exists_affine_posDef`). RH holds iff some positive-definite
function on the affine group of `ℚ` restricts on the dilations `x ↦ rx`, `r ∈ ℚ_{>0}`, to the
spline correlation `r ↦ C(−log r)`. Both directions pass through the dilations alone
(`riemannHypothesis_iff_isPosDefOnGroup_ratCorr`, via the rational Hecke orbit criterion).

So an affine (successor and dilation) carrier adds no positivity and no obstruction beyond the
dilation Gram: the successor coordinates of a positive functional are free, and can be set to
zero. A forcing law on the affine group must prescribe the successor part of the functional from
the arithmetic source. Over `𝔽_q` the same law shows that no positive-definite function on any
group restricts on a copy of `ℤ` to the golden trace sequence (`not_exists_posDef_golden`).
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-! ### Positive-definite functions on groups -/

section Group

open scoped Classical

variable {G : Type*} [Group G]

/-- Positive definiteness on a group: every Gram form `Σ c̄_a φ(x_a⁻¹ x_b) c_b` is real and
nonnegative. -/
def IsPosDefOnGroup (φ : G → ℂ) : Prop :=
  ∀ (N : ℕ) (x : Fin N → G) (c : Fin N → ℂ),
    ∃ r : ℝ, 0 ≤ r ∧ ∑ a, ∑ b, star (c a) * φ ((x a)⁻¹ * x b) * c b = r

/-- The Gram form over any finite index type. -/
theorem IsPosDefOnGroup.form {φ : G → ℂ} (hφ : IsPosDefOnGroup φ) {κ : Type*} [Fintype κ]
    (x : κ → G) (c : κ → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ a, ∑ b, star (c a) * φ ((x a)⁻¹ * x b) * c b = r := by
  set e := (Fintype.equivFin κ).symm
  obtain ⟨r, hr, h⟩ := hφ (Fintype.card κ) (x ∘ e) (c ∘ e)
  refine ⟨r, hr, ?_⟩
  rw [← h, ← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← e.sum_comp]
  rfl

/-- Positive definiteness pulls back along group homomorphisms. -/
theorem IsPosDefOnGroup.comp_hom {K : Type*} [Group K] {φ : G → ℂ} (hφ : IsPosDefOnGroup φ)
    (f : K →* G) : IsPosDefOnGroup (φ ∘ f) := by
  intro N x c
  obtain ⟨r, hr, h⟩ := hφ N (fun a => f (x a)) c
  exact ⟨r, hr, by simpa [map_mul, map_inv] using h⟩

/-- Restriction to a subgroup. -/
theorem IsPosDefOnGroup.restrict {φ : G → ℂ} (hφ : IsPosDefOnGroup φ) (H : Subgroup G) :
    IsPosDefOnGroup fun h : H => φ h :=
  hφ.comp_hom H.subtype

/-- A function on a subgroup extended by zero. -/
def extendFromSubgroup (H : Subgroup G) (ψ : H → ℂ) (g : G) : ℂ :=
  if h : g ∈ H then ψ ⟨g, h⟩ else 0

/-- The left-coset representative of `x`. -/
def leftCosetRep (H : Subgroup G) (x : G) : G := (QuotientGroup.mk x : G ⧸ H).out

theorem leftCosetRep_inv_mul_mem (H : Subgroup G) (x : G) : (leftCosetRep H x)⁻¹ * x ∈ H :=
  QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x : G ⧸ H))

theorem leftCosetRep_eq_iff (H : Subgroup G) (x y : G) :
    leftCosetRep H x = leftCosetRep H y ↔ x⁻¹ * y ∈ H := by
  unfold leftCosetRep
  constructor
  · intro h
    have := congrArg (QuotientGroup.mk : G → G ⧸ H) h
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
    exact QuotientGroup.eq.mp this
  · intro h
    congr 1
    exact QuotientGroup.eq.mpr h

/-- The `H`-part `h(x) = r(x)⁻¹ x` of `x`. -/
def cosetPart (H : Subgroup G) (x : G) : H := ⟨(leftCosetRep H x)⁻¹ * x, leftCosetRep_inv_mul_mem H x⟩

/-- **Induction.** The extension by zero of a positive-definite function on a subgroup is positive
definite on the group. -/
theorem isPosDefOnGroup_extendFromSubgroup {H : Subgroup G} {ψ : H → ℂ}
    (hψ : IsPosDefOnGroup ψ) : IsPosDefOnGroup (extendFromSubgroup H ψ) := by
  classical
  intro N x c
  set R := Finset.univ.image fun a => leftCosetRep H (x a)
  set c' : G → Fin N → ℂ := fun ρ a => if leftCosetRep H (x a) = ρ then c a else 0
  have hsplit : ∀ a b, star (c a) * extendFromSubgroup H ψ ((x a)⁻¹ * x b) * c b =
      ∑ ρ ∈ R, star (c' ρ a) * ψ ((cosetPart H (x a))⁻¹ * cosetPart H (x b)) * c' ρ b := by
    intro a b
    have ha : leftCosetRep H (x a) ∈ R := Finset.mem_image_of_mem _ (Finset.mem_univ a)
    by_cases hab : leftCosetRep H (x a) = leftCosetRep H (x b)
    · have hmem : (x a)⁻¹ * x b ∈ H := (leftCosetRep_eq_iff H _ _).mp hab
      have hpart : ((cosetPart H (x a))⁻¹ * cosetPart H (x b) : H) = ⟨(x a)⁻¹ * x b, hmem⟩ := by
        ext
        simp only [cosetPart, Subgroup.coe_mul, Subgroup.coe_inv, hab, mul_inv_rev, inv_inv]
        group
      rw [Finset.sum_eq_single_of_mem _ ha]
      · simp only [c', if_pos rfl, if_pos hab.symm, hpart, extendFromSubgroup]
        rw [dif_pos hmem]
      · intro ρ _ hρ
        simp only [c', if_neg (Ne.symm hρ), star_zero, zero_mul]
    · have hnot : (x a)⁻¹ * x b ∉ H := fun h => hab ((leftCosetRep_eq_iff H _ _).mpr h)
      rw [extendFromSubgroup, dif_neg hnot, mul_zero, zero_mul]
      refine (Finset.sum_eq_zero fun ρ _ => ?_).symm
      simp only [c']
      by_cases h1 : leftCosetRep H (x a) = ρ
      · have h2 : ¬ leftCosetRep H (x b) = ρ := fun h2 => hab (h1.trans h2.symm)
        simp only [if_neg h2, mul_zero]
      · simp only [if_neg h1, star_zero, zero_mul]
  have hρ : ∀ ρ ∈ R, ∃ r : ℝ, 0 ≤ r ∧ ∑ a, ∑ b, star (c' ρ a) *
      ψ ((cosetPart H (x a))⁻¹ * cosetPart H (x b)) * c' ρ b = r :=
    fun ρ _ => hψ.form (fun a => cosetPart H (x a)) (c' ρ)
  choose! r hr0 hr using hρ
  refine ⟨∑ ρ ∈ R, r ρ, Finset.sum_nonneg hr0, ?_⟩
  set F : G → Fin N → Fin N → ℂ := fun ρ a b =>
    star (c' ρ a) * ψ ((cosetPart H (x a))⁻¹ * cosetPart H (x b)) * c' ρ b
  calc ∑ a, ∑ b, star (c a) * extendFromSubgroup H ψ ((x a)⁻¹ * x b) * c b
      = ∑ a, ∑ b, ∑ ρ ∈ R, F ρ a b := by simp_rw [hsplit]; rfl
    _ = ∑ a, ∑ ρ ∈ R, ∑ b, F ρ a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ ρ ∈ R, ∑ a, ∑ b, F ρ a b := Finset.sum_comm
    _ = ∑ ρ ∈ R, ((r ρ : ℝ) : ℂ) := Finset.sum_congr rfl fun ρ hρ' => hr ρ hρ'
    _ = ((∑ ρ ∈ R, r ρ : ℝ) : ℂ) := by push_cast; rfl

/-- **Restriction–induction law.** A function on a subgroup extends to a positive-definite
function on the group iff it is positive definite on the subgroup. -/
theorem exists_isPosDefOnGroup_extension_iff (H : Subgroup G) (ψ : H → ℂ) :
    (∃ φ : G → ℂ, IsPosDefOnGroup φ ∧ ∀ h : H, φ h = ψ h) ↔ IsPosDefOnGroup ψ := by
  constructor
  · rintro ⟨φ, hφ, hres⟩
    have := hφ.restrict H
    simp_rw [hres] at this
    exact this
  · intro hψ
    refine ⟨extendFromSubgroup H ψ, isPosDefOnGroup_extendFromSubgroup hψ, fun h => ?_⟩
    simp [extendFromSubgroup]

end Group

/-! ### The affine group of `ℚ` -/

/-- The affine group `x ↦ ax + b` of `ℚ`. -/
abbrev AffineGroupQ : Type := ℚ ≃ᵃ[ℚ] ℚ

/-- The dilation `x ↦ ux`. -/
def dilation : ℚˣ →* AffineGroupQ := AffineEquiv.homothetyUnitsMulHom 0

/-- The successor `x ↦ x + 1`. -/
def successor : AffineGroupQ := AffineEquiv.constVAdd ℚ ℚ (1 : ℚ)

theorem dilation_apply (u : ℚˣ) (x : ℚ) : dilation u x = u * x := by
  simp [dilation, AffineMap.homothety_apply]

theorem successor_apply (x : ℚ) : successor x = 1 + x := by
  simp [successor, vadd_eq_add]

/-- The two ring operations do not commute. -/
theorem dilation_mul_successor_ne :
    dilation (Units.mk0 2 two_ne_zero) * successor ≠ successor * dilation (Units.mk0 2 two_ne_zero) := by
  intro h
  have := congrArg (fun e : AffineGroupQ => e 0) h
  simp only [AffineEquiv.coe_mul, Function.comp_apply, dilation_apply, successor_apply] at this
  norm_num at this

theorem dilation_injective : Function.Injective dilation := by
  intro u v h
  have := congrArg (fun e : AffineGroupQ => e 1) h
  simp only [dilation_apply, mul_one] at this
  exact Units.ext this

/-- The positive rationals as a subgroup of `ℚˣ`. -/
def posUnits : Subgroup ℚˣ where
  carrier := {u | 0 < (u : ℚ)}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    exact mul_pos ha hb
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    rw [Units.val_inv_eq_inv_val]
    exact inv_pos.mpr ha

open Matrix ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

/-- The logarithm of a positive rational unit. -/
def logPos (u : posUnits) : ℝ := Real.log ((u : ℚˣ) : ℚ)

theorem logPos_inv_mul (u v : posUnits) : logPos (u⁻¹ * v) = logPos v - logPos u := by
  have hu : (0 : ℝ) < (((u : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast u.2
  have hv : (0 : ℝ) < (((v : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast v.2
  simp only [logPos, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  push_cast
  rw [Real.log_mul (inv_pos.mpr hu).ne' hv.ne', Real.log_inv]
  ring

/-- The spline correlation on the positive rationals, `r ↦ C(−log r)`. -/
def ratCorr (u : posUnits) : ℂ := splineCorr (-logPos u)

/-- The Gram form of the Toeplitz matrix over rational shifts is the Gram form of `ratCorr`. -/
theorem dotProduct_weilGram_eq_ratCorr {κ : Type*} [Fintype κ] (x : κ → posUnits) (c : κ → ℂ) :
    star c ⬝ᵥ (weilGram vonMangoldtWeight (fun a => ArithmeticCastelnuovoSeveri.translate
      (logPos (x a)) (cx cubicSpline)) *ᵥ c) =
      ∑ a, ∑ b, star (c a) * ratCorr ((x a)⁻¹ * x b) * c b := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [weilGram_translate_cubicSpline, ratCorr, logPos_inv_mul, neg_sub]
  ring

open scoped ComplexOrder in
/-- **RH is positive definiteness of the spline correlation on `ℚ_{>0}`.** -/
theorem riemannHypothesis_iff_isPosDefOnGroup_ratCorr :
    RiemannHypothesis ↔ IsPosDefOnGroup ratCorr := by
  constructor
  · intro hRH N x c
    set f : Fin N → ℝ → ℂ := fun a => ArithmeticCastelnuovoSeveri.translate (logPos (x a))
      (cx cubicSpline)
    have hneg : hermNegIndex (weilGram vonMangoldtWeight f) = 0 := by
      have h := negIndex_weilGram_le_offLineCount f
        (fun a => translate_contDiff (cx_contDiff contDiff_cubicSpline) _)
        (fun a => translate_hasCompactSupport (cx_hasCompactSupport hasCompactSupport_cubicSpline) _)
      rw [riemannHypothesis_iff_no_rightZero.mp hRH, Set.encard_empty] at h
      exact_mod_cast nonpos_iff_eq_zero.mp h
    have hpsd := (hermNegIndex_eq_zero_iff_posSemidef' (weilGram_isHermitian _ f)).mp hneg
    have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 c
    rw [dotProduct_weilGram_eq_ratCorr] at hq
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hq
    exact ⟨_, hre, Complex.ext rfl (by simpa using him.symm)⟩
  · intro hφ
    rw [riemannHypothesis_iff_splineRatHecke_negIndex_eq_zero]
    intro S hS
    have hx : ∀ s : S, ∃ u : posUnits, logPos u = s := by
      intro s
      obtain ⟨r, hr, hlog⟩ := hS s.2
      refine ⟨⟨Units.mk0 r hr.ne', hr⟩, ?_⟩
      simp [logPos, hlog]
    choose x hx using hx
    have hfam : (fun s : S => ArithmeticCastelnuovoSeveri.translate s (cx cubicSpline)) =
        fun s => ArithmeticCastelnuovoSeveri.translate (logPos (x s)) (cx cubicSpline) :=
      funext fun s => by rw [hx s]
    rw [hfam, hermNegIndex_eq_zero_iff_posSemidef' (weilGram_isHermitian _ _),
      Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨weilGram_isHermitian _ _, fun v => ?_⟩
    obtain ⟨r, hr, hsum⟩ := hφ.form x v
    rw [dotProduct_weilGram_eq_ratCorr, hsum]
    exact_mod_cast hr

/-- The dilation subgroup `{x ↦ rx : r ∈ ℚ_{>0}}` of the affine group. -/
def dilationSubgroup : Subgroup AffineGroupQ := posUnits.map dilation

theorem exists_eq_dilation (h : dilationSubgroup) : ∃ u : posUnits, dilation u = h := by
  obtain ⟨u, hu, huh⟩ := Subgroup.mem_map.mp h.2
  exact ⟨⟨u, hu⟩, huh⟩

/-- The spline correlation read on the dilation subgroup. -/
def dilationCorr (h : dilationSubgroup) : ℂ := ratCorr (exists_eq_dilation h).choose

theorem dilationCorr_dilation (u : posUnits) :
    dilationCorr ⟨dilation u, Subgroup.mem_map_of_mem _ u.2⟩ = ratCorr u := by
  unfold dilationCorr
  congr 1
  apply Subtype.ext
  exact dilation_injective (exists_eq_dilation _).choose_spec

theorem isPosDefOnGroup_dilationCorr_iff : IsPosDefOnGroup dilationCorr ↔ IsPosDefOnGroup ratCorr := by
  set d : posUnits →* dilationSubgroup :=
    { toFun := fun u => ⟨dilation u, Subgroup.mem_map_of_mem _ u.2⟩
      map_one' := by ext; simp
      map_mul' := fun u v => by ext; simp }
  have hcomp : dilationCorr ∘ d = ratCorr := funext fun u => dilationCorr_dilation u
  constructor
  · intro h
    rw [← hcomp]
    exact h.comp_hom d
  · intro h N y c
    have hy : ∀ a, ∃ u : posUnits, dilation u = y a := fun a => exists_eq_dilation (y a)
    choose u hu using hy
    obtain ⟨r, hr, hsum⟩ := h N u c
    refine ⟨r, hr, ?_⟩
    rw [← hsum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 2
    rw [← hcomp]
    simp only [Function.comp_apply]
    congr 1
    apply Subtype.ext
    simp only [d, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
      map_inv, hu]

/-- **RH on the affine group.** RH holds iff some positive-definite function on the affine group of
`ℚ` restricts on the dilations `x ↦ rx`, `r ∈ ℚ_{>0}`, to the spline correlation. -/
theorem riemannHypothesis_iff_exists_affine_posDef :
    RiemannHypothesis ↔ ∃ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ ∧
      ∀ u : posUnits, φ (dilation u) = ratCorr u := by
  rw [riemannHypothesis_iff_isPosDefOnGroup_ratCorr, ← isPosDefOnGroup_dilationCorr_iff,
    ← exists_isPosDefOnGroup_extension_iff]
  constructor
  · rintro ⟨φ, hφ, hres⟩
    exact ⟨φ, hφ, fun u => by
      rw [← dilationCorr_dilation u]
      exact hres ⟨dilation u, Subgroup.mem_map_of_mem _ u.2⟩⟩
  · rintro ⟨φ, hφ, hres⟩
    refine ⟨φ, hφ, fun h => ?_⟩
    obtain ⟨u, hu⟩ := exists_eq_dilation h
    have hh : h = ⟨dilation u, Subgroup.mem_map_of_mem _ u.2⟩ := Subtype.ext hu.symm
    rw [hh, dilationCorr_dilation]
    exact hres u

/-! ### The golden datum on any group -/

/-- A real positive-definite function on `Multiplicative ℤ` gives an even positive-definite
function on `ℤ`. -/
theorem isEvenPosDef_of_isPosDefOnGroup {τ : ℤ → ℝ} (heven : ∀ m, τ (-m) = τ m)
    (h : IsPosDefOnGroup fun m : Multiplicative ℤ => (τ m.toAdd : ℂ)) :
    MultiplicativePositivityGeometry.IsEvenPosDef τ where
  even := heven
  posDef n x c := by
    obtain ⟨r, hr, hsum⟩ := h n (fun a => Multiplicative.ofAdd (x a)) (fun a => (c a : ℂ))
    have e : (∑ a, ∑ b, star ((c a : ℂ)) * (τ (Multiplicative.toAdd
        ((Multiplicative.ofAdd (x a))⁻¹ * Multiplicative.ofAdd (x b))) : ℂ) * (c b : ℂ)) =
        ((∑ a, ∑ b, c a * c b * τ (x a - x b) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Complex.star_def, Complex.conj_ofReal]
      rw [show -x a + x b = -(x a - x b) by ring, heven]
      ring
    rw [e] at hsum
    have := Complex.ofReal_injective hsum
    rw [this]
    exact hr

/-- **The golden datum has no positive-definite carrier.** No positive-definite function on any
group restricts on a copy of `ℤ` to the golden trace sequence. -/
theorem not_exists_posDef_golden {G : Type*} [Group G] (ι : Multiplicative ℤ →* G) :
    ¬ ∃ φ : G → ℂ, IsPosDefOnGroup φ ∧
      ∀ m : Multiplicative ℤ, φ (ι m) =
        (CurveDatum'.traceSeq ArithmeticCastelnuovoSeveri.goldenDatum m.toAdd : ℂ) := by
  rintro ⟨φ, hφ, hres⟩
  have h := hφ.comp_hom ι
  have e : φ ∘ ι = fun m : Multiplicative ℤ =>
      (CurveDatum'.traceSeq ArithmeticCastelnuovoSeveri.goldenDatum m.toAdd : ℂ) := funext hres
  rw [e] at h
  exact CurveDatum'.not_isEvenPosDef_goldenDatum_traceSeq
    (isEvenPosDef_of_isPosDefOnGroup (fun m => by simp [CurveDatum'.traceSeq]) h)

end GaloisForLFunctions.ArithmeticPositiveDuality
