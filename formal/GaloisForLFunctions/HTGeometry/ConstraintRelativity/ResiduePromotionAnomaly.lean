import Mathlib
import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility
import GaloisForLFunctions.RHTower.MobiusThetaSourceDaggerMinimalBoundaryLaw
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology

/-!
# The residue-preserving law-promotion anomaly

Let `C` be a chain complex of vector spaces, `R : C_n → W` a residue cocycle (`R d = 0`), and
`Z : V → ker d_n` a family of defect cycles.  Attaching law cells means adjoining `V` in degree
`n+1` with `d'(x, v) = d x + Z v`.

The residue survives the attachment unchanged exactly when `R Z = 0`.  When `R Z ≠ 0` the
attachment must add a compensator space `A` in degree `n` with `R Z + S q = 0`, which forces
`dim A ≥ rank (R Z)`, with equality realised by `A = im (R Z)`.  So the promotion anomaly rank is
exactly `rank (R Z)`.  A rank-minimal fitted compensator with invertible `q` splits the extension
as the original complex plus a contractible two-term complex carrying no residue, so it is a
re-presentation and not a law birth.  The rank is invariant under any comparison identifying the
descended residues and the defect classes.

Two size laws follow for function-valued compensators.  A subspace of functions closed under
multiplication by the coordinate and containing a function with infinitely many nonzeros is
infinite-dimensional.  And no holomorphic function can equal `-(n^{2\Re s - 1} - 1)c(s)` on an open
connected set where the holomorphic factor `c` is nonvanishing, because the exponential factor
depends on `s` only through `\Re s`.  Before imposing the reflection diagonal the same charge has
holomorphic separation rank exactly two.
-/

noncomputable section

namespace HTGeometry.ConstraintRelativity

open scoped ComplexConjugate

/-! ## Theorem 1: the no-surplus attachment criterion -/

section Attachment

variable {k C1 C0 V W A : Type*} [Field k]
variable [AddCommGroup C1] [Module k C1] [AddCommGroup C0] [Module k C0]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup A] [Module k A]

/-- The differential of the cell-attached complex: old boundaries plus the attached defects. -/
def attachedDifferential (d : C1 →ₗ[k] C0) (Z : V →ₗ[k] C0) : C1 × V →ₗ[k] C0 :=
  d.coprod Z

@[simp] theorem attachedDifferential_apply (d : C1 →ₗ[k] C0) (Z : V →ₗ[k] C0) (w : C1 × V) :
    attachedDifferential d Z w = d w.1 + Z w.2 := rfl

/-- **Theorem 1, card `(5)` boxed.**  The residue extends unchanged to the cell-attached complex
exactly when it annihilates the attached defects. -/
theorem attachedDifferential_residue_cocycle_iff (d : C1 →ₗ[k] C0) (Z : V →ₗ[k] C0)
    (R : C0 →ₗ[k] W) (hR : R.comp d = 0) :
    R.comp (attachedDifferential d Z) = 0 ↔ R.comp Z = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    have := LinearMap.congr_fun h ((0 : C1), v)
    simpa using this
  · intro h
    apply LinearMap.ext
    intro w
    have h1 := LinearMap.congr_fun hR w.1
    have h2 := LinearMap.congr_fun h w.2
    simp only [LinearMap.comp_apply, attachedDifferential_apply, map_add,
      LinearMap.zero_apply] at h1 h2 ⊢
    rw [h1, h2, add_zero]

/-- **Theorem 1, second clause.**  A residue-preserving attachment kills every defect class exactly
when the residue vanishes on the defect subspace. -/
theorem attachedDifferential_residue_cocycle_iff_range (d : C1 →ₗ[k] C0) (Z : V →ₗ[k] C0)
    (R : C0 →ₗ[k] W) (hR : R.comp d = 0) :
    R.comp (attachedDifferential d Z) = 0 ↔ LinearMap.range Z ≤ LinearMap.ker R := by
  rw [attachedDifferential_residue_cocycle_iff d Z R hR]
  constructor
  · rintro h _ ⟨v, rfl⟩
    exact LinearMap.congr_fun h v
  · intro h
    apply LinearMap.ext
    intro v
    exact h ⟨v, rfl⟩

/-! ## Theorem 2: the minimal compensator rank -/

/-- The compensated differential: attached defects together with their compensator components. -/
def compensatedDifferential (d : C1 →ₗ[k] C0) (Z : V →ₗ[k] C0) (q : V →ₗ[k] A) :
    C1 × V →ₗ[k] C0 × A :=
  (d.coprod Z).prod ((0 : C1 →ₗ[k] A).coprod q)

@[simp] theorem compensatedDifferential_apply (d : C1 →ₗ[k] C0) (Z : V →ₗ[k] C0)
    (q : V →ₗ[k] A) (w : C1 × V) :
    compensatedDifferential d Z q w = (d w.1 + Z w.2, q w.2) := by
  refine Prod.ext rfl ?_
  change (0 : C0 → A) (d w.1 + Z w.2) + q w.2 = q w.2
  simp

/-- **Theorem 2, card `(7)` boxed.**  The extended residue is a cocycle exactly when the
compensator carries the opposite residue. -/
theorem compensatedDifferential_residue_cocycle_iff (d : C1 →ₗ[k] C0) (Z : V →ₗ[k] C0)
    (q : V →ₗ[k] A) (R : C0 →ₗ[k] W) (S : A →ₗ[k] W) (hR : R.comp d = 0) :
    (R.coprod S).comp (compensatedDifferential d Z q) = 0 ↔ R.comp Z + S.comp q = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    have := LinearMap.congr_fun h ((0 : C1), v)
    simpa using this
  · intro h
    apply LinearMap.ext
    intro w
    have h1 := LinearMap.congr_fun hR w.1
    have h2 := LinearMap.congr_fun h w.2
    simp only [LinearMap.comp_apply, compensatedDifferential_apply, LinearMap.coprod_apply,
      map_add, LinearMap.zero_apply, LinearMap.add_apply] at h1 h2 ⊢
    rw [h1, zero_add]
    exact h2

/-- **Theorem 2, card `(8)`.**  A compensator carrying the opposite residue has rank at least the
anomaly rank. -/
theorem rank_le_of_compensates (Z : V →ₗ[k] C0) (q : V →ₗ[k] A) (R : C0 →ₗ[k] W)
    (S : A →ₗ[k] W) (h : R.comp Z + S.comp q = 0) :
    LinearMap.range (R.comp Z) ≤ LinearMap.range S := by
  rintro _ ⟨v, rfl⟩
  refine ⟨-(q v), ?_⟩
  have := LinearMap.congr_fun h v
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at this
  rw [map_neg]
  change -S (q v) = R (Z v)
  exact neg_eq_of_add_eq_zero_left this

/-- **Theorem 2, card `(9)` boxed.**  The anomaly rank is achieved: the image of `R Z` is itself a
compensator carrying the opposite residue. -/
theorem exists_minimal_compensator (Z : V →ₗ[k] C0) (R : C0 →ₗ[k] W) :
    ∃ (q : V →ₗ[k] LinearMap.range (R.comp Z))
      (S : LinearMap.range (R.comp Z) →ₗ[k] W),
      R.comp Z + S.comp q = 0 ∧ Function.Surjective q := by
  refine ⟨(R.comp Z).rangeRestrict, -(LinearMap.range (R.comp Z)).subtype, ?_,
    (R.comp Z).surjective_rangeRestrict⟩
  apply LinearMap.ext
  intro v
  simp

end Attachment

/-! ## Theorem 3: minimal fitted compensation is derived-trivial -/

section Fitted

variable {k C1 C0 V A : Type*} [Field k]
variable [AddCommGroup C1] [Module k C1] [AddCommGroup C0] [Module k C0]
variable [AddCommGroup V] [Module k V] [AddCommGroup A] [Module k A]

/-- **Card `(13)`.**  The degree-`n` change of coordinates that splits a fitted compensation. -/
def fittedSplitting (Z : V →ₗ[k] C0) (e : V ≃ₗ[k] A) : (C0 × A) ≃ₗ[k] (C0 × A) where
  toFun w := (w.1 - Z (e.symm w.2), w.2)
  invFun w := (w.1 + Z (e.symm w.2), w.2)
  map_add' w v := by
    refine Prod.ext ?_ rfl
    change w.1 + v.1 - Z (e.symm (w.2 + v.2)) = (w.1 - Z (e.symm w.2)) + (v.1 - Z (e.symm v.2))
    rw [map_add, map_add]
    abel
  map_smul' c w := by
    refine Prod.ext ?_ rfl
    change c • w.1 - Z (e.symm (c • w.2)) = c • (w.1 - Z (e.symm w.2))
    rw [map_smul, map_smul, smul_sub]
  left_inv w := by
    refine Prod.ext ?_ rfl
    change w.1 - Z (e.symm w.2) + Z (e.symm w.2) = w.1
    abel
  right_inv w := by
    refine Prod.ext ?_ rfl
    change w.1 + Z (e.symm w.2) - Z (e.symm w.2) = w.1
    abel

@[simp] theorem fittedSplitting_apply (Z : V →ₗ[k] C0) (e : V ≃ₗ[k] A) (w : C0 × A) :
    fittedSplitting Z e w = (w.1 - Z (e.symm w.2), w.2) := rfl

@[simp] theorem fittedSplitting_symm_apply (Z : V →ₗ[k] C0) (e : V ≃ₗ[k] A) (w : C0 × A) :
    (fittedSplitting Z e).symm w = (w.1 + Z (e.symm w.2), w.2) := rfl

/-- **Theorem 3, card `(14)`.**  After the change of coordinates the compensated differential is
the direct sum of the original differential and the invertible compensator map: the extension is
the original complex plus a contractible two-term complex. -/
theorem fittedSplitting_compensatedDifferential (d : C1 →ₗ[k] C0) (Z : V →ₗ[k] C0)
    (e : V ≃ₗ[k] A) (w : C1 × V) :
    fittedSplitting Z e (compensatedDifferential d Z (e : V →ₗ[k] A) w) = (d w.1, e w.2) := by
  rw [compensatedDifferential_apply, fittedSplitting_apply]
  refine Prod.ext ?_ rfl
  change d w.1 + Z w.2 - Z (e.symm (e w.2)) = d w.1
  rw [e.symm_apply_apply]
  abel

/-- **Theorem 3, card `(15)`.**  In the split coordinates the extended residue is the original
residue on the original complex and zero on the contractible summand. -/
theorem fittedSplitting_residue {W : Type*} [AddCommGroup W] [Module k W]
    (Z : V →ₗ[k] C0) (e : V ≃ₗ[k] A) (R : C0 →ₗ[k] W) (w : C0 × A) :
    (R.coprod (-(R.comp (Z.comp (e.symm : A →ₗ[k] V))))) ((fittedSplitting Z e).symm w) =
      R w.1 := by
  rw [fittedSplitting_symm_apply, LinearMap.coprod_apply]
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, map_add, LinearEquiv.coe_coe]
  abel

end Fitted

/-! ## Theorem 4: presentation invariance of the anomaly rank -/

section Invariance

variable {k C0 C0' V W : Type*} [Field k]
variable [AddCommGroup C0] [Module k C0] [AddCommGroup C0'] [Module k C0']
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **Theorem 4, card `(17)`.**  A comparison that matches the residues and carries the defect
cycles to the defect cycles gives literally the same anomaly map, hence the same rank. -/
theorem anomalyMap_eq_of_comparison (R : C0 →ₗ[k] W) (R' : C0' →ₗ[k] W)
    (F : C0 →ₗ[k] C0') (Z : V →ₗ[k] C0) (Z' : V →ₗ[k] C0')
    (hres : R'.comp F = R) (hdef : F.comp Z = Z') :
    R.comp Z = R'.comp Z' := by
  rw [← hres, ← hdef, LinearMap.comp_assoc]

theorem anomalyRank_eq_of_comparison (R : C0 →ₗ[k] W) (R' : C0' →ₗ[k] W)
    (F : C0 →ₗ[k] C0') (Z : V →ₗ[k] C0) (Z' : V →ₗ[k] C0')
    (hres : R'.comp F = R) (hdef : F.comp Z = Z') :
    Module.finrank k (LinearMap.range (R.comp Z)) =
      Module.finrank k (LinearMap.range (R'.comp Z')) := by
  rw [anomalyMap_eq_of_comparison R R' F Z Z' hres hdef]

end Invariance

/-! ## The literal arithmetic specialization -/

/-- **Card `(26)` boxed.**  For a nonzero scalar coefficient the anomaly map of the one-dimensional
defect is zero exactly on the critical line: the anomaly rank is `0` there and `1` off it. -/
theorem anomaly_scalar_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) {c : ℂ} (hc : c ≠ 0) (r : ℝ) :
    ((n : ℝ) ^ (2 * r - 1) - 1 : ℝ) * c = 0 ↔ r = 1 / 2 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn.trans_lt' one_lt_two
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · have hpow : (n : ℝ) ^ (2 * r - 1) = 1 := by
        have := sub_eq_zero.mp (by exact_mod_cast h1 : ((n : ℝ) ^ (2 * r - 1) - 1 : ℝ) = 0)
        exact this
      have hzero : 2 * r - 1 = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : (n : ℝ) ^ (2 * r - 1) < (n : ℝ) ^ (0 : ℝ) :=
            Real.rpow_lt_rpow_of_exponent_lt hn1 hlt
          rw [Real.rpow_zero, hpow] at this
          exact lt_irrefl 1 this
        · have : (n : ℝ) ^ (0 : ℝ) < (n : ℝ) ^ (2 * r - 1) :=
            Real.rpow_lt_rpow_of_exponent_lt hn1 hgt
          rw [Real.rpow_zero, hpow] at this
          exact lt_irrefl 1 this
      linarith
    · exact absurd h2 hc
  · rintro rfl
    norm_num

/-! ## Theorem 5: coordinate-stable compensators are infinite-dimensional -/

section SizeLaw

variable {U : Type*}

/-- The coordinate powers of a function with infinitely many nonzero values are linearly
independent. -/
theorem linearIndependent_coordinatePowers (z : U → ℂ) (f : U → ℂ)
    (hinf : {w : ℂ | ∃ u : U, z u = w ∧ f u ≠ 0}.Infinite) :
    LinearIndependent ℂ (fun j : ℕ => (fun u => (z u) ^ j * f u : U → ℂ)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  set p : Polynomial ℂ := ∑ j ∈ s, Polynomial.monomial j (c j) with hp
  have hroots : {w : ℂ | ∃ u : U, z u = w ∧ f u ≠ 0} ⊆ {x : ℂ | p.IsRoot x} := by
    rintro w ⟨u, rfl, hfu⟩
    have hev := congrFun hsum u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
    have hfac : (∑ j ∈ s, c j * (z u) ^ j) * f u = 0 := by
      rw [Finset.sum_mul]
      rw [← hev]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hpoly : ∑ j ∈ s, c j * (z u) ^ j = 0 :=
      (mul_eq_zero.mp hfac).resolve_right hfu
    show p.eval (z u) = 0
    rw [hp, Polynomial.eval_finsetSum]
    simpa [Polynomial.eval_monomial] using hpoly
  have hpzero : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p (hinf.mono hroots)
  have hcoeff : p.coeff i = c i := by
    rw [hp, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro j _ hji
      rw [Polynomial.coeff_monomial, if_neg hji]
    · intro hni
      exact absurd hi hni
  rw [← hcoeff, hpzero, Polynomial.coeff_zero]

/-- **Theorem 5, card `(18)`.**  A space of functions closed under multiplication by the spectral
coordinate and containing one function with infinitely many nonzero values is
infinite-dimensional. -/
theorem not_finiteDimensional_of_coordinateStable (z : U → ℂ) (S : Submodule ℂ (U → ℂ))
    (hstable : ∀ g ∈ S, (fun u => z u * g u) ∈ S) (f : U → ℂ) (hf : f ∈ S)
    (hinf : {w : ℂ | ∃ u : U, z u = w ∧ f u ≠ 0}.Infinite) :
    ¬ FiniteDimensional ℂ S := by
  intro hfd
  have hmem : ∀ j : ℕ, (fun u => (z u) ^ j * f u : U → ℂ) ∈ S := by
    intro j
    induction j with
    | zero => simpa using hf
    | succ m ih =>
      have hnext := hstable _ ih
      have hfun : (fun u => z u * ((z u) ^ m * f u)) =
          (fun u => (z u) ^ (m + 1) * f u) := by
        funext u
        ring
      rwa [hfun] at hnext
  have hli : LinearIndependent ℂ (fun j : ℕ => (⟨_, hmem j⟩ : S)) := by
    refine LinearIndependent.of_comp S.subtype ?_
    exact linearIndependent_coordinatePowers z f hinf
  haveI := hli.finite_of_isNoetherian
  exact not_finite ℕ

end SizeLaw

/-! ## Theorem 6: no holomorphic compensator before divisor specialization -/

section Holomorphic

/-- The real exponential factor of the defect charge. -/
def defectFactor (n : ℕ) (x : ℝ) : ℝ := (n : ℝ) ^ (2 * x - 1) - 1

theorem defectFactor_injective {n : ℕ} (hn : 2 ≤ n) : Function.Injective (defectFactor n) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn.trans_lt' one_lt_two
  intro x y hxy
  have hpow : (n : ℝ) ^ (2 * x - 1) = (n : ℝ) ^ (2 * y - 1) := by
    have := hxy
    rw [defectFactor, defectFactor, sub_left_injective.eq_iff] at this
    exact this
  by_contra hne
  have hne' : 2 * x - 1 ≠ 2 * y - 1 := by
    intro h
    exact hne (by linarith)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · exact absurd hpow (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hn1 hlt))
  · exact absurd hpow.symm (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hn1 hgt))

/-- **Theorem 6, cards `(19)`–`(21)`.**  No holomorphic function equals the mixed defect charge on
a connected open set where the holomorphic factor is nonvanishing: the charge depends on `s` only
through `Re s`, so agreeing with it on one vertical segment forces it to agree everywhere, and then
`Re s` would be locally constant. -/
theorem no_holomorphic_defectCompensator {n : ℕ} (hn : 2 ≤ n) {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) {c h : ℂ → ℂ}
    (hc : AnalyticOnNhd ℂ c Ω) (hh : AnalyticOnNhd ℂ h Ω)
    (hne : ∀ s ∈ Ω, c s ≠ 0) {s₀ : ℂ} (hs₀ : s₀ ∈ Ω)
    (heq : ∀ s ∈ Ω, h s = -((defectFactor n s.re : ℝ) : ℂ) * c s) :
    False := by
  set lam : ℝ := defectFactor n s₀.re with hlam
  set H : ℂ → ℂ := fun s => h s + (lam : ℂ) * c s with hH
  have hHan : AnalyticOnNhd ℂ H Ω := hh.add (analyticOnNhd_const.mul hc)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ s₀ hs₀
  set u : ℕ → ℂ := fun m => s₀ + Complex.I * ((1 : ℝ) / (m + 1) : ℝ) with hu
  have hutend : Filter.Tendsto u Filter.atTop (nhds s₀) := by
    have h0 : Filter.Tendsto (fun m : ℕ => ((1 : ℝ) / (m + 1) : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (Complex.continuous_ofReal.tendsto 0).comp h0
    have hmul : Filter.Tendsto (fun m : ℕ => Complex.I * (((1 : ℝ) / (m + 1) : ℝ) : ℂ))
        Filter.atTop (nhds 0) := by
      simpa using (this.const_mul Complex.I)
    simpa [hu] using (hmul.const_add s₀)
  have hune : ∀ m : ℕ, u m ≠ s₀ := by
    intro m hm
    have : Complex.I * (((1 : ℝ) / (m + 1) : ℝ) : ℂ) = 0 := by
      have := hm
      rw [hu] at this
      simpa using this
    rcases mul_eq_zero.mp this with h1 | h2
    · exact Complex.I_ne_zero h1
    · have hpos : (0 : ℝ) < (1 : ℝ) / (m + 1) := by positivity
      have : ((1 : ℝ) / (m + 1) : ℝ) = 0 := by exact_mod_cast h2
      linarith
  have hure : ∀ m : ℕ, (u m).re = s₀.re := by
    intro m
    simp [hu]
  have hmemΩ : ∀ᶠ m in Filter.atTop, u m ∈ Ω :=
    hutend.eventually (hΩ.mem_nhds hs₀)
  have hHzero : ∀ᶠ m in Filter.atTop, H (u m) = 0 := by
    filter_upwards [hmemΩ] with m hm
    rw [hH]
    simp only
    rw [heq (u m) hm, hure m]
    ring
  have hfreq : ∃ᶠ z in nhdsWithin s₀ {s₀}ᶜ, H z = 0 := by
    have htendW : Filter.Tendsto u Filter.atTop (nhdsWithin s₀ {s₀}ᶜ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hutend
        (Filter.Eventually.of_forall fun m => hune m)
    exact htendW.frequently hHzero.frequently
  have hHeq := hHan.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn hs₀ hfreq
  have hconst : ∀ s ∈ Ω, defectFactor n s.re = lam := by
    intro s hs
    have hHs : H s = 0 := hHeq hs
    rw [hH] at hHs
    simp only at hHs
    rw [heq s hs] at hHs
    have hfac : ((lam : ℂ) - ((defectFactor n s.re : ℝ) : ℂ)) * c s = 0 := by
      linear_combination hHs
    rcases mul_eq_zero.mp hfac with h1 | h2
    · have : (lam : ℂ) = ((defectFactor n s.re : ℝ) : ℂ) := by
        linear_combination h1
      exact_mod_cast this.symm
    · exact absurd h2 (hne s hs)
  have hmove : s₀ + ((ε / 2 : ℝ) : ℂ) ∈ Ω := by
    apply hball
    rw [Metric.mem_ball, Complex.dist_eq]
    simp only [add_sub_cancel_left]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hre : defectFactor n (s₀ + ((ε / 2 : ℝ) : ℂ)).re = lam := hconst _ hmove
  have hreval : (s₀ + ((ε / 2 : ℝ) : ℂ)).re = s₀.re + ε / 2 := by simp
  rw [hreval] at hre
  have hinj := defectFactor_injective hn (a₁ := s₀.re + ε / 2) (a₂ := s₀.re) (by rw [hre, hlam])
  linarith

end Holomorphic

/-! ## Theorem 7: the mixed charge has separation rank exactly two -/

section Separation

/-- **Card `(22)`.**  The mixed defect charge before imposing the reflection diagonal. -/
def mixedCharge (n : ℕ) (c : ℂ → ℂ) (s t : ℂ) : ℂ :=
  ((n : ℂ) ^ (s + t - 1) - 1) * c s

/-- **Card `(23)`.**  Two separated legs suffice. -/
theorem mixedCharge_two_legs {n : ℕ} (hn : (n : ℂ) ≠ 0) (c : ℂ → ℂ) (s t : ℂ) :
    mixedCharge n c s t =
      ((n : ℂ) ^ (s - 1 / 2) * c s) * (n : ℂ) ^ (t - 1 / 2) - c s := by
  rw [mixedCharge, show s + t - 1 = (s - 1 / 2) + (t - 1 / 2) by ring,
    Complex.cpow_add _ _ hn]
  ring

/-- The evaluation determinant of the mixed charge. -/
theorem mixedCharge_det {n : ℕ} (hn : (n : ℂ) ≠ 0) (c : ℂ → ℂ) (s₁ s₂ t₁ t₂ : ℂ) :
    mixedCharge n c s₁ t₁ * mixedCharge n c s₂ t₂ -
        mixedCharge n c s₁ t₂ * mixedCharge n c s₂ t₁ =
      c s₁ * c s₂ *
        ((n : ℂ) ^ (s₁ - 1 / 2) - (n : ℂ) ^ (s₂ - 1 / 2)) *
        ((n : ℂ) ^ (t₂ - 1 / 2) - (n : ℂ) ^ (t₁ - 1 / 2)) := by
  rw [mixedCharge_two_legs hn, mixedCharge_two_legs hn, mixedCharge_two_legs hn,
    mixedCharge_two_legs hn]
  ring

/-- **Theorem 7, card `(24)`.**  The mixed charge is not a product of one leg in `s` and one leg in
`t`: its separation rank is at least two, hence exactly two by `mixedCharge_two_legs`. -/
theorem mixedCharge_not_rankOne {n : ℕ} (hn : (n : ℂ) ≠ 0) (c : ℂ → ℂ)
    {s₁ s₂ t₁ t₂ : ℂ} (hc₁ : c s₁ ≠ 0) (hc₂ : c s₂ ≠ 0)
    (hs : (n : ℂ) ^ (s₁ - 1 / 2) ≠ (n : ℂ) ^ (s₂ - 1 / 2))
    (ht : (n : ℂ) ^ (t₁ - 1 / 2) ≠ (n : ℂ) ^ (t₂ - 1 / 2))
    (f g : ℂ → ℂ)
    (hfac : ∀ s t : ℂ, s = s₁ ∨ s = s₂ → t = t₁ ∨ t = t₂ →
      mixedCharge n c s t = f s * g t) :
    False := by
  have hdet := mixedCharge_det hn c s₁ s₂ t₁ t₂
  rw [hfac s₁ t₁ (Or.inl rfl) (Or.inl rfl), hfac s₂ t₂ (Or.inr rfl) (Or.inr rfl),
    hfac s₁ t₂ (Or.inl rfl) (Or.inr rfl), hfac s₂ t₁ (Or.inr rfl) (Or.inl rfl)] at hdet
  have hzero : c s₁ * c s₂ *
      ((n : ℂ) ^ (s₁ - 1 / 2) - (n : ℂ) ^ (s₂ - 1 / 2)) *
      ((n : ℂ) ^ (t₂ - 1 / 2) - (n : ℂ) ^ (t₁ - 1 / 2)) = 0 := by
    rw [← hdet]
    ring
  rcases mul_eq_zero.mp hzero with h1 | h2
  · rcases mul_eq_zero.mp h1 with h3 | h4
    · rcases mul_eq_zero.mp h3 with h5 | h6
      · exact absurd h5 hc₁
      · exact absurd h6 hc₂
    · exact hs (sub_eq_zero.mp h4)
  · exact ht (sub_eq_zero.mp h2).symm

/-- Two points of an open set with distinct exponential legs. -/
theorem exists_separating_point {n : ℕ} (hn : 2 ≤ n) {U : Set ℂ} (hU : IsOpen U) {s₁ : ℂ}
    (hs₁ : s₁ ∈ U) :
    ∃ s₂ ∈ U, (n : ℂ) ^ (s₁ - 1 / 2) ≠ (n : ℂ) ^ (s₂ - 1 / 2) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn.trans_lt' one_lt_two
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU s₁ hs₁
  refine ⟨s₁ + ((ε / 2 : ℝ) : ℂ), hball ?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq]
    simp only [add_sub_cancel_left]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · rw [show s₁ + ((ε / 2 : ℝ) : ℂ) - 1 / 2 = (s₁ - 1 / 2) + ((ε / 2 : ℝ) : ℂ) by ring,
      Complex.cpow_add _ _ hn0]
    intro heq
    have hXne : (n : ℂ) ^ (s₁ - 1 / 2) ≠ 0 := by
      intro h0
      exact hn0 ((Complex.cpow_eq_zero_iff _ _).mp h0).1
    have hone : (n : ℂ) ^ ((ε / 2 : ℝ) : ℂ) = 1 := by
      have hcancel : (n : ℂ) ^ (s₁ - 1 / 2) * 1 =
          (n : ℂ) ^ (s₁ - 1 / 2) * (n : ℂ) ^ ((ε / 2 : ℝ) : ℂ) := by
        rw [mul_one]
        exact heq
      exact (mul_right_cancel₀ hXne (by linear_combination hcancel)).symm
    have hreal : (n : ℂ) ^ ((ε / 2 : ℝ) : ℂ) = (((n : ℝ) ^ (ε / 2 : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity)]
    rw [hreal] at hone
    have : (n : ℝ) ^ (ε / 2 : ℝ) = 1 := by exact_mod_cast hone
    have hgt : (1 : ℝ) < (n : ℝ) ^ (ε / 2 : ℝ) :=
      Real.one_lt_rpow_iff_of_pos (by linarith) |>.mpr (Or.inl ⟨hnR, by linarith⟩)
    linarith

/-- **Theorem 7 on open sets.**  On any product of open sets where the holomorphic factor is
nonvanishing, the mixed charge admits no separated factorization. -/
theorem mixedCharge_not_rankOne_on_open {n : ℕ} (hn : 2 ≤ n) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) {s₁ t₁ : ℂ} (hs₁ : s₁ ∈ U) (ht₁ : t₁ ∈ V)
    (c : ℂ → ℂ) (hc : ∀ s ∈ U, c s ≠ 0) (f g : ℂ → ℂ)
    (hfac : ∀ s ∈ U, ∀ t ∈ V, mixedCharge n c s t = f s * g t) : False := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  obtain ⟨s₂, hs₂, hs⟩ := exists_separating_point hn hU hs₁
  obtain ⟨t₂, ht₂, ht⟩ := exists_separating_point hn hV ht₁
  refine mixedCharge_not_rankOne hn0 c (hc s₁ hs₁) (hc s₂ hs₂) hs ht f g ?_
  rintro s t (rfl | rfl) (rfl | rfl)
  · exact hfac _ hs₁ _ ht₁
  · exact hfac _ hs₁ _ ht₂
  · exact hfac _ hs₂ _ ht₁
  · exact hfac _ hs₂ _ ht₂

end Separation

/-! ## Theorem 5 for the actual completed theta source -/

section XiSource

open RHTower
open RHTower.SlabFullWidthAdmissibility

/-- The completed theta source is nonvanishing on an infinite set. -/
theorem infinite_xiC_nonvanishing :
    {w : ℂ | ∃ u : ℂ, u = w ∧ XiC u ≠ 0}.Infinite := by
  have hinj : Set.InjOn (fun t : ℝ => (t : ℂ) * Complex.I) (Set.Ici (1 : ℝ)) := by
    intro a _ b _ hab
    have him : ((a : ℂ) * Complex.I).im = a := by simp
    have him' : ((b : ℂ) * Complex.I).im = b := by simp
    rw [← him, ← him']
    exact congrArg Complex.im hab
  have hsub : (fun t : ℝ => (t : ℂ) * Complex.I) '' (Set.Ici (1 : ℝ)) ⊆
      {w : ℂ | ∃ u : ℂ, u = w ∧ XiC u ≠ 0} := by
    rintro _ ⟨t, ht, rfl⟩
    have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
    refine ⟨_, rfl, RHTower.SlabFullWidthAdmissibility.XiC_ne_zero_of_half_le_abs_im ?_⟩
    have him : ((t : ℂ) * Complex.I).im = t := by simp
    rw [him, abs_of_nonneg (by linarith)]
    linarith
  exact Set.Infinite.mono hsub ((Set.infinite_image_iff hinj).mpr (Set.Ici_infinite 1))

/-- **Theorem 5, card `(18)` instantiated.**  Any compensator realization containing the actual
completed theta source and stable under multiplication by the spectral coordinate is
infinite-dimensional. -/
theorem not_finiteDimensional_of_xiC_coordinateStable (S : Submodule ℂ (ℂ → ℂ))
    (hstable : ∀ g ∈ S, (fun z : ℂ => z * g z) ∈ S) (hXi : (XiC : ℂ → ℂ) ∈ S) :
    ¬ FiniteDimensional ℂ S :=
  not_finiteDimensional_of_coordinateStable (fun z : ℂ => z) S hstable XiC hXi
    infinite_xiC_nonvanishing

end XiSource

/-! ## The literal arithmetic defect -/

section LiteralSource

open RHTower
open GaloisForLFunctions.HTGeometry

/-- **Card `(26)` boxed, literal form.**  For the ordinary-prime trace-one cycle the anomaly map of
the physical cyclic-to-paracyclic defect vanishes exactly on the critical line, so the promotion
anomaly rank is `0` there and `1` off it. -/
theorem literal_defect_anomaly_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport)
    (x : CCMRationalAdelicDegreeOneCyclicSource)
    (hx : ccmRationalAdelicDegreeOneTrace x = 1) :
    ccmRationalAdelicTwoLegCyclicResidue
        (cyclicParacyclicEquivarianceDefect
          ccmRationalAdelicDegreeOneCyclicRotation
          (sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
          (ccmMobiusThetaXiJetTwoLegLanding (xiSupportMultiplicity rho)
            (xiSpectralPointSupport rho)) x) = 0 ↔ (rho : ℂ).re = 1 / 2 := by
  rw [ccmMobiusThetaTwoLegParacyclicDefect_residue, hx, mul_one]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with h1 | h2
    · have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 := by
        have : ((deningerHalfDensityMateGain n (rho : ℂ) : ℂ)) = 1 := by
          linear_combination h1
        exact_mod_cast this
      exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn (rho : ℂ)).mp hgain
    · exact absurd h2 (thetaInternalJetLeadingSourceCoefficient_ne_zero rho)
  · intro hre
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 :=
      (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn (rho : ℂ)).mpr hre
    rw [hgain]
    norm_num

end LiteralSource

end HTGeometry.ConstraintRelativity

end
