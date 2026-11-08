import GaloisForLFunctions.BlackHoleRingdown.TheCuspFormsAreGravitationalModes
import GaloisForLFunctions.RHTower.Gamma0MaassHeckeCoefficients
import GaloisForLFunctions.RHTower.DeckCuspidalOrthogonalEisenstein
import GaloisForLFunctions.RHTower.DeckPointPairSelbergTransform
import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport
import GaloisForLFunctions.RHTower.DeckCuspidalConstantTerm
import GaloisForLFunctions.HTGeometry.ModularDirichletFormDense

/-!
# The Hecke eigenforms of the cusp channel

The cusp channel of the modular horizon carries the arithmetic of the Hecke operators
`T_p f(z) = f(pz) + Σ_{b mod p} f((z+b)/p)`. For every eigenvalue `λ` of the cusp spectrum there is a
nonzero cusp form of eigenvalue `λ` that is an eigenfunction of every `T_p` at once
(`exists_heckeEigenform`).

**The cusp space.** `S(λ)` consists of the `SL₂(ℤ)`-invariant Maass eigenfunctions of eigenvalue `λ` that
tend to zero at the cusp and have zero constant term. Such a function is bounded, so it is a cuspidal `L²`
Laplace eigenfunction (`isCuspLaplaceEigen_vecOf`): cuspidality is the orthogonality to incomplete
Eisenstein series, which unfolds to the constant term.

**Finite dimension.** The `L²` class determines the function: a point-pair average sees only the class, and
by Selberg's principle it multiplies the eigenfunction by `h(s) ≠ 0` for a narrow unit kernel
(`eq_zero_of_toDeckL2_eq_zero`). Distinct Laplace eigenvalues are orthogonal, so the class lies in the span
of the finitely many basis vectors of eigenvalue `λ`. Hence `S(λ)` is finite-dimensional.

**Hecke.** `T_p` preserves invariance, the eigenvalue equation and cusp decay (corpus), and the constant
term: the zeroth coefficient of `T_p f` at `y` is that of `f` at `py` plus `p` times that at `y/p`. For
distinct primes `T_p T_q = T_q T_p`: both are `f(pqz) + Σ_c f((pz+c)/q) + Σ_b f((qz+b)/p) +
Σ_{m < pq} f((z+m)/pq)`, after reindexing `c ↦ pc mod q` and using periodicity. A commuting family on a
nonzero finite-dimensional complex space has a common eigenvector.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff MatrixGroups InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet GaloisForLFunctions.RHTower.Gamma0MaassHecke
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos atImInfty)
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace (Deck)

namespace HeckeCusp

/-! ### A common eigenvector of a commuting family -/

/-- **Commuting endomorphisms of a nonzero finite-dimensional complex space have a common
eigenvector.** -/
theorem exists_common_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ι : Type*} (T : ι → V →ₗ[ℂ] V) (hcomm : ∀ m n, T m ∘ₗ T n = T n ∘ₗ T m)
    (W : Submodule ℂ V) (hW : W ≠ ⊥) (hinv : ∀ n, ∀ w ∈ W, T n w ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ n, ∃ c : ℂ, T n v = c • v := by
  induction hd : Module.finrank ℂ W using Nat.strong_induction_on generalizing W with
  | _ d ih =>
    by_cases hscal : ∀ n, ∃ c : ℂ, ∀ w ∈ W, T n w = c • w
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨v, hv, hv0, fun n => let ⟨c, hc⟩ := hscal n; ⟨c, hc v hv⟩⟩
    · push Not at hscal
      obtain ⟨n₀, hn₀⟩ := hscal
      set S : W →ₗ[ℂ] W := (T n₀).restrict (hinv n₀) with hS
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue S
      obtain ⟨w₀, hw₀⟩ := hμ.exists_hasEigenvector
      set W' : Submodule ℂ V := W ⊓ LinearMap.ker (T n₀ - μ • LinearMap.id) with hW'
      have hmem : ∀ w, w ∈ W' ↔ w ∈ W ∧ T n₀ w = μ • w := by
        intro w
        simp [hW', sub_eq_zero]
      have hw₀mem : (w₀ : V) ∈ W' := by
        rw [hmem]
        refine ⟨w₀.2, ?_⟩
        have := hw₀.apply_eq_smul
        have h2 := congrArg Subtype.val this
        simpa [hS] using h2
      have hw₀ne : (w₀ : V) ≠ 0 := fun h => hw₀.2 (Subtype.ext h)
      have hW'ne : W' ≠ ⊥ := fun h => hw₀ne (by rw [h] at hw₀mem; simpa using hw₀mem)
      have hW'lt : W' < W := by
        refine lt_of_le_of_ne inf_le_left fun heq => ?_
        obtain ⟨w, hw, hne⟩ := hn₀ μ
        rw [← heq, hmem] at hw
        exact hne hw.2
      have hW'inv : ∀ n, ∀ w ∈ W', T n w ∈ W' := by
        intro n w hw
        rw [hmem] at hw ⊢
        refine ⟨hinv n w hw.1, ?_⟩
        have h1 := congrArg (fun L : V →ₗ[ℂ] V => L w) (hcomm n₀ n)
        simp only [LinearMap.coe_comp, Function.comp_apply] at h1
        rw [h1, hw.2, map_smul]
      have hlt : Module.finrank ℂ W' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hW'lt
      obtain ⟨v, hv, hv0, hvc⟩ := ih _ hlt W' hW'ne hW'inv rfl
      exact ⟨v, (Submodule.mem_inf.mp hv).1, hv0, hvc⟩

/-! ### The cusp space -/

/-- The constant term of a function on `ℍ` at height `y`. -/
def constTerm (g : UpperHalfPlane → ℂ) (y : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, g (ofComplex (SelbergMaassMean.point x y))

theorem continuous_of_maass {lam : ℝ} {g : UpperHalfPlane → ℂ} (hg : IsMaassEigenfunction lam g) :
    Continuous g := by
  have h := hg.1.continuousOn.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)
  refine h.congr fun z => ?_
  simp [UpperHalfPlane.ofComplex_apply]

theorem continuous_slice {lam : ℝ} {g : UpperHalfPlane → ℂ} (hg : IsMaassEigenfunction lam g) {y : ℝ}
    (hy : 0 < y) : Continuous fun x : ℝ => g (ofComplex (SelbergMaassMean.point x y)) := by
  have hp : Continuous fun x : ℝ => SelbergMaassMean.point x y := by
    unfold SelbergMaassMean.point
    fun_prop
  have hmaps : ∀ x : ℝ, SelbergMaassMean.point x y ∈ {z : ℂ | 0 < z.im} := fun x => by
    show 0 < (SelbergMaassMean.point x y).im
    simp [SelbergMaassMean.point, hy]
  exact hg.1.continuousOn.comp_continuous hp hmaps

theorem isMaassEigenfunction_smul {lam : ℝ} {g : UpperHalfPlane → ℂ} (hg : IsMaassEigenfunction lam g)
    (c : ℂ) : IsMaassEigenfunction lam (c • g) := by
  set L : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ c with hL
  have hcomp : (c • g) ∘ ofComplex = fun x => L ((g ∘ ofComplex) x) := by
    funext x
    simp [hL]
  refine ⟨?_, fun z => ?_⟩
  · unfold IsRealSmoothUpperHalfPlane
    rw [hcomp]
    exact L.contDiff.comp_contDiffOn hg.1
  · have hG : ContDiffAt ℝ 2 (g ∘ ofComplex) (z : ℂ) :=
      hg.1.contDiffAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos)
    unfold positiveHyperbolicLaplacian
    rw [hcomp, CuspGravity.fderiv_fderiv_clm L hG 1, CuspGravity.fderiv_fderiv_clm L hG I]
    have he := hg.2 z
    unfold positiveHyperbolicLaplacian at he
    simp only [hL, ContinuousLinearMap.mul_apply', Pi.smul_apply, smul_eq_mul]
    linear_combination c * he

/-- **The cusp space of eigenvalue `λ`.** -/
def cuspSpace (lam : ℝ) : Submodule ℂ (UpperHalfPlane → ℂ) where
  carrier := {g | (∀ (A : SL(2, ℤ)) (z : UpperHalfPlane), g (A • z) = g z) ∧ IsMaassEigenfunction lam g ∧
    UpperHalfPlane.IsZeroAtImInfty g ∧ ∀ y : ℝ, 0 < y → constTerm g y = 0}
  add_mem' := by
    rintro g h ⟨hg1, hg2, hg3, hg4⟩ ⟨hh1, hh2, hh3, hh4⟩
    refine ⟨fun A z => by rw [Pi.add_apply, Pi.add_apply, hg1, hh1], isMaassEigenfunction_add hg2 hh2, hg3.add hh3,
      fun y hy => ?_⟩
    unfold constTerm at hg4 hh4 ⊢
    simp only [Pi.add_apply]
    rw [intervalIntegral.integral_add ((continuous_slice hg2 hy).intervalIntegrable _ _)
      ((continuous_slice hh2 hy).intervalIntegrable _ _), hg4 y hy, hh4 y hy, add_zero]
  zero_mem' := by
    refine ⟨fun A z => rfl, isMaassEigenfunction_zero lam, (tendsto_const_nhds : Tendsto (fun _ : UpperHalfPlane => (0 : ℂ)) atImInfty (𝓝 0)),
      fun y _ => ?_⟩
    simp [constTerm]
  smul_mem' := by
    rintro c g ⟨hg1, hg2, hg3, hg4⟩
    refine ⟨fun A z => by rw [Pi.smul_apply, Pi.smul_apply, hg1], isMaassEigenfunction_smul hg2 c, hg3.smul c,
      fun y hy => ?_⟩
    unfold constTerm at hg4 ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul, hg4 y hy, mul_zero]

theorem mem_cuspSpace {lam : ℝ} {g : UpperHalfPlane → ℂ} :
    g ∈ cuspSpace lam ↔ (∀ (A : SL(2, ℤ)) (z : UpperHalfPlane), g (A • z) = g z) ∧
      IsMaassEigenfunction lam g ∧ UpperHalfPlane.IsZeroAtImInfty g ∧ ∀ y : ℝ, 0 < y → constTerm g y = 0 :=
  Iff.rfl

/-! ### Cusp forms are bounded -/

theorem exists_bound {lam : ℝ} {g : UpperHalfPlane → ℂ} (hg : g ∈ cuspSpace lam) :
    ∃ C : ℝ, ∀ z, ‖g z‖ ≤ C := by
  obtain ⟨hinv, hmaass, hzero, -⟩ := hg
  have hc := continuous_of_maass hmaass
  have hev : ∀ᶠ z in atImInfty, ‖g z‖ ≤ 1 :=
    (hzero.norm.eventually (Iio_mem_nhds (by simp : ‖(0 : ℂ)‖ < 1))).mono fun _ h => le_of_lt h
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 hev
  set Y : ℝ := max A 1
  set K : Set ℂ := Icc (-(1 / 2)) (1 / 2) ×ℂ Icc (1 / 2) Y
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKU : K ⊆ GaloisForLFunctions.HTGeometry.upperSet := by
    intro w hw
    have := (Complex.mem_reProdIm.mp hw).2.1
    show 0 < w.im
    linarith
  have hK := GaloisForLFunctions.HTGeometry.isCompact_preimage_coe hKc hKU
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 1 B, fun z => ?_⟩
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  rw [← hinv γ z]
  by_cases hY : A ≤ (γ • z).im
  · exact (hA _ hY).trans (le_max_left _ _)
  · push Not at hY
    have hmem : (γ • z) ∈ UpperHalfPlane.coe ⁻¹' K := by
      refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
      · exact abs_le.mp hγ.2
      · exact ⟨(OddCusp.half_lt_im_of_mem_fd hγ).le, le_trans hY.le (le_max_left _ _)⟩
    exact (hB _ hmem).trans (le_max_right _ _)

/-! ### The bridge to the cuspidal `L²` eigenfunctions -/

/-- The level-one field of a scalar function. -/
def vecOf (g : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : DeckSpace 0 := g z • onesVec 0

theorem vecOf_apply (g : UpperHalfPlane → ℂ) (z : UpperHalfPlane) (q : Deck 0) : vecOf g z q = g z := by
  simp [vecOf, onesVec]

section Bridge

variable {lam : ℝ} {g : UpperHalfPlane → ℂ} (hg : g ∈ cuspSpace lam)
include hg

theorem contDiffOn_vecOf : ContDiffOn ℝ 2 (fun ζ => vecOf g (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im} := by
  have hs : ContDiff ℝ 2 fun w : ℂ => w • onesVec 0 :=
    (contDiff_id.smul contDiff_const : ContDiff ℂ 2 fun w : ℂ => id w • onesVec 0).restrict_scalars ℝ
  exact hs.comp_contDiffOn hg.2.1.1

theorem continuous_vecOf : Continuous (vecOf g) :=
  (continuous_of_maass hg.2.1).smul continuous_const

theorem deckEquivariant_vecOf : deckEquivariant 0 (vecOf g) := by
  intro A z
  rw [vecOf, vecOf, hg.1 A z, map_smul, OddCusp.regular_onesVec]

theorem memLp_vecOf : MemLp (vecOf g) 2 MaassCongruenceL2.cellMeasure := by
  obtain ⟨C, hC⟩ := exists_bound hg
  refine OddCusp.memLp_of_eqOn_fd (continuous_vecOf hg) (C := C * ‖onesVec 0‖) (fun z => ?_)
    fun z _ => rfl
  rw [vecOf, norm_smul]
  exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)

theorem levelCuspZero_vecOf : levelCuspZero 0 (vecOf g) := by
  intro q y hy a
  have hper : Function.Periodic (fun x : ℝ => vecOf g (ofComplex (SelbergMaassMean.point x y)) q) 1 := by
    intro x
    simp only [vecOf_apply]
    have hT : ofComplex (SelbergMaassMean.point (x + 1) y) =
        ModularGroup.T • ofComplex (SelbergMaassMean.point x y) := by
      have hpos : ∀ t : ℝ, 0 < (SelbergMaassMean.point t y).im := fun t => by
        simp [SelbergMaassMean.point, hy]
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd, ofComplex_apply_of_im_pos (hpos _),
        ofComplex_apply_of_im_pos (hpos _)]
      simp [SelbergMaassMean.point]
      ring
    rw [hT, hg.1]
  have h0 : ∫ x in (0 : ℝ)..1, vecOf g (ofComplex (SelbergMaassMean.point x y)) q = 0 := by
    simp only [vecOf_apply]
    exact hg.2.2.2 y hy
  rw [show a + (((0 : ℕ) + 1 : ℕ) : ℝ) = a + 1 by norm_num, hper.intervalIntegral_add_eq a 0, zero_add, h0]

theorem cuspidal_vecOf : toDeckL2 (vecOf g) (memLp_vecOf hg) ∈ cuspidalL2Closure 0 := by
  refine (mem_cuspidalL2Closure_iff _).2
    ⟨toDeckL2_mem_deckCentralFixedL2 (deckEquivariant_vecOf hg) (memLp_vecOf hg), fun ψ v hv => ?_⟩
  have h := inner_incEisL2 ψ hv (MemLp.coeFn_toLp (memLp_vecOf hg)) (continuous_vecOf hg)
    (deckEquivariant_vecOf hg)
  refine h.trans ?_
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℂ)) fun y hy => by
      rw [horoAverage_eq_zero (continuous_vecOf hg) (deckEquivariant_vecOf hg) (levelCuspZero_vecOf hg) hv hy,
        mul_zero, smul_zero]]
  simp

theorem eigen_vecOf (z : UpperHalfPlane) : hypLap (vecOf g) z = ((-lam : ℝ) : ℂ) • vecOf g z := by
  ext q
  rw [hypLap_apply (contDiffOn_vecOf hg) z q]
  have hcomp : (fun w => vecOf g w q) = g := funext fun w => vecOf_apply g w q
  rw [hcomp, hg.2.1.2 z, PiLp.smul_apply, vecOf_apply, smul_eq_mul]
  push_cast
  ring

/-- **A function of the cusp space is a cuspidal `L²` Laplace eigenfunction.** -/
theorem isCuspLaplaceEigen_vecOf : IsCuspLaplaceEigen 0 lam (vecOf g) :=
  ⟨contDiffOn_vecOf hg, deckEquivariant_vecOf hg, memLp_vecOf hg, cuspidal_vecOf hg, eigen_vecOf hg⟩

/-- **The `L²` class determines the cusp form.** A point-pair average sees only the class and, by
Selberg's principle, multiplies the eigenfunction by `h(s) ≠ 0` for a narrow unit kernel. -/
theorem eq_zero_of_toDeckL2_eq_zero (h0 : toDeckL2 (vecOf g) (memLp_vecOf hg) = 0) : g = 0 := by
  obtain ⟨s, hs⟩ := exists_spectral_parameter lam
  have hR : (0 : ℝ) < 1 / (512 * (‖s‖ ^ 2 + 1)) := by positivity
  obtain ⟨P, hPR, hP0, hPm⟩ := exists_smoothUnitProfile hR
  have hRle : P.radius * (512 * (‖s‖ ^ 2 + 1)) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hPR
    linarith
  have hh := CuspSpectrum.norm_selbergTransform_sub_one_le P hP0 hPm (by positivity) hRle le_rfl
  have hne : selbergTransform P.toFun s ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg, norm_one] at hh
    norm_num at hh
  have hae : vecOf g =ᵐ[MaassCongruenceL2.cellMeasure] 0 := by
    have h1 := MemLp.coeFn_toLp (memLp_vecOf hg)
    have h2 : ⇑(toDeckL2 (vecOf g) (memLp_vecOf hg)) =ᵐ[MaassCongruenceL2.cellMeasure] 0 := by
      rw [h0]
      exact Lp.coeFn_zero _ _ _
    exact h1.symm.trans h2
  have heig : ∀ z, hypLap (vecOf g) z = (-(s * (1 - s))) • vecOf g z := by
    intro z
    rw [eigen_vecOf hg z, hs]
    push_cast
    rfl
  funext z
  have hpp := ppApply_eigen P.contDiff_two.continuous P.kernelSupport (contDiffOn_vecOf hg)
    (deckEquivariant_vecOf hg) heig z
  rw [ppApply_congr_ae _ hae] at hpp
  have hzero : ppApply P.toFun (0 : UpperHalfPlane → DeckSpace 0) z = 0 := by
    simp [ppApply, ppTerm]
  rw [hzero] at hpp
  have hv : vecOf g z = 0 := (smul_eq_zero.mp hpp.symm).resolve_left hne
  have := congrArg (fun v : DeckSpace 0 => v (1 : Deck 0)) hv
  simpa [vecOf_apply] using this

end Bridge

/-! ### Finite dimension -/

/-- The span of the basis vectors of eigenvalue `λ`. -/
def eigSpan (lam : ℝ) : Submodule ℂ (DeckL2 0) :=
  Submodule.span ℂ (Set.range fun j : {j : CuspEigenIndex 0 // j.1 = lam} =>
    ((cuspEigenBasis 0 j : CuspidalL2 0) : DeckL2 0))

theorem finite_eigenIndex (lam : ℝ) : Finite {j : CuspEigenIndex 0 // j.1 = lam} :=
  ((finite_cuspEigenIndex_le lam).subset fun j (hj : j.1 = lam) => le_of_eq hj).to_subtype

instance (lam : ℝ) : FiniteDimensional ℂ (eigSpan lam) := by
  haveI := finite_eigenIndex lam
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem toDeckL2_vecOf_mem {lam : ℝ} {g : UpperHalfPlane → ℂ} (hg : g ∈ cuspSpace lam) :
    toDeckL2 (vecOf g) (memLp_vecOf hg) ∈ eigSpan lam := by
  classical
  set e : CuspEigenIndex 0 → DeckL2 0 := fun j => ((cuspEigenBasis 0 j : CuspidalL2 0) : DeckL2 0) with he
  set W := toDeckL2 (vecOf g) (memLp_vecOf hg) with hWdef
  have hWc : W ∈ cuspidalL2Closure 0 := cuspidal_vecOf hg
  have horth : ∀ k j, ⟪e k, e j⟫_ℂ = if k = j then 1 else 0 := fun k j => by
    show ⟪((cuspEigenBasis 0 k : CuspidalL2 0) : DeckL2 0), ((cuspEigenBasis 0 j : CuspidalL2 0) : DeckL2 0)⟫_ℂ = _
    rw [← Submodule.coe_inner]
    exact orthonormal_iff_ite.mp (cuspEigenBasis 0).orthonormal k j
  have hzero : ∀ j : CuspEigenIndex 0, j.1 ≠ lam → ⟪e j, W⟫_ℂ = 0 := by
    intro j hj
    show ⟪((cuspEigenBasis 0 j : CuspidalL2 0) : DeckL2 0), W⟫_ℂ = 0
    rw [(cuspEigenBasis_spec j).choose_spec.choose_spec]
    exact inner_toDeckL2_eq_zero_of_ne (cuspEigenBasis_spec j).choose_spec.choose
      (isCuspLaplaceEigen_vecOf hg) hj
  have hfin := (finite_cuspEigenIndex_le lam).subset fun j (hj : j.1 = lam) => le_of_eq hj
  set S := hfin.toFinset with hS
  set R := W - ∑ j ∈ S, ⟪e j, W⟫_ℂ • e j with hR
  have hRc : R ∈ cuspidalL2Closure 0 :=
    Submodule.sub_mem _ hWc (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (cuspEigenBasis 0 j).2)
  have hRk : ∀ k, ⟪e k, R⟫_ℂ = 0 := by
    intro k
    rw [hR, inner_sub_right, inner_sum]
    simp_rw [inner_smul_right, horth, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · ring
    · have : k.1 ≠ lam := fun h => hk (hfin.mem_toFinset.mpr h)
      rw [hzero k this, sub_zero]
  have hR0 : R = 0 := by
    have hr : (⟨R, hRc⟩ : CuspidalL2 0) = 0 := by
      apply (cuspEigenBasis 0).repr.injective
      rw [map_zero]
      ext k
      rw [HilbertBasis.repr_apply_apply, Submodule.coe_inner]
      exact hRk k
    exact congrArg Subtype.val hr
  have hW : W = ∑ j ∈ S, ⟪e j, W⟫_ℂ • e j := sub_eq_zero.mp hR0
  rw [hW]
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hfin.mem_toFinset.mp hj⟩, rfl⟩)

/-- The `L²` class as a linear map into the span. -/
def toSpan (lam : ℝ) : cuspSpace lam →ₗ[ℂ] eigSpan lam where
  toFun g := ⟨toDeckL2 (vecOf g.1) (memLp_vecOf g.2), toDeckL2_vecOf_mem g.2⟩
  map_add' g h := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_vecOf (g + h).2), MemLp.coeFn_toLp (memLp_vecOf g.2),
      MemLp.coeFn_toLp (memLp_vecOf h.2),
      Lp.coeFn_add (toDeckL2 (vecOf g.1) (memLp_vecOf g.2)) (toDeckL2 (vecOf h.1) (memLp_vecOf h.2))]
      with z h1 h2 h3 h4
    simp only [Submodule.coe_add] at h1 ⊢
    rw [toDeckL2, h1, h4, Pi.add_apply, toDeckL2, toDeckL2, h2, h3, vecOf, vecOf, vecOf, Pi.add_apply,
      add_smul]
  map_smul' c g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_vecOf (c • g).2), MemLp.coeFn_toLp (memLp_vecOf g.2),
      Lp.coeFn_smul c (toDeckL2 (vecOf g.1) (memLp_vecOf g.2))] with z h1 h2 h3
    simp only [SetLike.val_smul, RingHom.id_apply] at h1 ⊢
    rw [toDeckL2, h1, h3, Pi.smul_apply, toDeckL2, h2, vecOf, vecOf, Pi.smul_apply, smul_eq_mul, mul_smul]

theorem toSpan_injective (lam : ℝ) : Function.Injective (toSpan lam) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  apply Subtype.ext
  have h0 : toDeckL2 (vecOf g.1) (memLp_vecOf g.2) = 0 := congrArg Subtype.val hg
  exact eq_zero_of_toDeckL2_eq_zero g.2 h0

/-- **The cusp space is finite-dimensional.** -/
instance (lam : ℝ) : FiniteDimensional ℂ (cuspSpace lam) :=
  Module.Finite.of_injective (toSpan lam) (toSpan_injective lam)

/-! ### The Hecke operators on the cusp space -/

section Hecke

variable {lam : ℝ}

theorem ofComplex_add_one {w : ℂ} (hw : 0 < w.im) :
    ofComplex (w + 1) = ModularGroup.T • ofComplex w := by
  have hw1 : 0 < (w + 1).im := by simpa using hw
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd, ofComplex_apply_of_im_pos hw1,
    ofComplex_apply_of_im_pos hw]
  push_cast
  ring

theorem periodic_comp {g : UpperHalfPlane → ℂ} (hg : g ∈ cuspSpace lam) :
    ∀ w : ℂ, 0 < w.im → (g ∘ ofComplex) (w + 1) = (g ∘ ofComplex) w := fun w hw => by
  simp only [Function.comp]
  rw [ofComplex_add_one hw, hg.1]

theorem periodic_nat {F : ℂ → ℂ} (hper : ∀ w : ℂ, 0 < w.im → F (w + 1) = F w) {w : ℂ} (hw : 0 < w.im)
    (k : ℕ) : F (w + k) = F w := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 0 < (w + k).im := by simpa using hw
    rw [Nat.cast_succ, ← add_assoc, hper _ hk, ih]

theorem coefficient_zero (F : ℂ → ℂ) (y : ℝ) :
    SelbergMaassFourier.coefficient 1 0 F y = ∫ x in (0 : ℝ)..1, F (SelbergMaassMean.point x y) := by
  simp [SelbergMaassFourier.coefficient, _root_.RHTower.deningerFourierCoeff,
    _root_.RHTower.deningerFourierKernel]

variable (p : ℕ) [hp : Fact p.Prime]

theorem heckeH_comp_ofComplex (g : UpperHalfPlane → ℂ) {w : ℂ} (hw : 0 < w.im) :
    heckeH p g (ofComplex w) = heckeT p (g ∘ ofComplex) w := by
  rw [heckeH_eq, ofComplex_apply_of_im_pos hw]

/-- **`T_p` preserves the cusp space.** -/
theorem heckeH_mem_cuspSpace {g : UpperHalfPlane → ℂ} (hg : g ∈ cuspSpace lam) :
    heckeH p g ∈ cuspSpace lam := by
  have hinv : g ∈ upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma0 1)) := by
    rw [mem_upperHalfPlaneInvariantFunctions]
    intro γ z
    obtain ⟨σ, -, hσ⟩ := Subgroup.mem_map.1 γ.2
    rw [← hσ, SelbergMaassCuspTransport.integral_action]
    exact hg.1 σ z
  have hinvH := heckeH_mem p (Nat.coprime_one_right p) hinv
  rw [mem_upperHalfPlaneInvariantFunctions] at hinvH
  have hcusp : IsCuspidalAtIntegralCusps g := by
    intro σ
    have : (fun z : UpperHalfPlane => g (integralSL2ToReal σ • z)) = g := funext fun z => by
      rw [SelbergMaassCuspTransport.integral_action, hg.1]
    rw [this]
    exact hg.2.2.1
  have hterm : ∀ i : Option (ZMod p),
      IsMaassEigenfunction lam (fun w => g ((alphaQ p i).map (algebraMap ℚ ℝ) • w)) ∧
        IsCuspidalAtIntegralCusps (fun w => g ((alphaQ p i).map (algebraMap ℚ ℝ) • w)) :=
    fun i => rationalGL_maass_eigenfunction_cuspidal_pullback (alphaQ p i) (alphaQ_det_pos p i)
      lam g hg.2.1 hcusp
  have hmaass : IsMaassEigenfunction lam (heckeH p g) :=
    isMaassEigenfunction_sum Finset.univ _ fun i _ => (hterm i).1
  have hcuspH : IsCuspidalAtIntegralCusps (heckeH p g) :=
    isCuspidal_sum Finset.univ _ fun i _ => (hterm i).2
  refine ⟨fun A z => ?_, hmaass, ?_, fun y hy => ?_⟩
  · have hA : A ∈ CongruenceSubgroup.Gamma0 1 :=
      CongruenceSubgroup.Gamma0_mem.2 (Subsingleton.elim _ _)
    have h := hinvH ⟨integralSL2ToReal A, Subgroup.mem_map_of_mem _ hA⟩ z
    rwa [show ((⟨integralSL2ToReal A, Subgroup.mem_map_of_mem _ hA⟩ :
        realImage (CongruenceSubgroup.Gamma0 1)) : SL2R) • z = A • z from
      SelbergMaassCuspTransport.integral_action A z] at h
  · have h1 := hcuspH 1
    have : (fun z : UpperHalfPlane => heckeH p g (integralSL2ToReal 1 • z)) = heckeH p g := funext fun z => by
      rw [SelbergMaassCuspTransport.integral_action, one_smul]
    rwa [this] at h1
  · have hF : ContinuousOn (g ∘ ofComplex) {z : ℂ | 0 < z.im} := hg.2.1.1.continuousOn
    have hcoef := coefficient_heckeT (p := p) hF (periodic_comp hg) 0 hy
    simp only [dvd_zero, if_true, Int.zero_ediv, mul_zero] at hcoef
    rw [coefficient_zero, coefficient_zero, coefficient_zero] at hcoef
    have h1 : ∫ x in (0 : ℝ)..1, (g ∘ ofComplex) (SelbergMaassMean.point x (p * y)) = 0 :=
      hg.2.2.2 _ (by have := hp.out.pos; positivity)
    have h2 : ∫ x in (0 : ℝ)..1, (g ∘ ofComplex) (SelbergMaassMean.point x (y / p)) = 0 :=
      hg.2.2.2 _ (by have := hp.out.pos; positivity)
    rw [h1, h2, mul_zero, add_zero] at hcoef
    unfold constTerm
    rw [← hcoef]
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact heckeH_comp_ofComplex p g (by simp [SelbergMaassMean.point, hy])

/-- `T_p` on the cusp space. -/
def heckeLin : cuspSpace lam →ₗ[ℂ] cuspSpace lam where
  toFun g := ⟨heckeH p g.1, heckeH_mem_cuspSpace p g.2⟩
  map_add' g h := Subtype.ext <| funext fun z => by
    simp [heckeH, Finset.sum_add_distrib]
  map_smul' c g := Subtype.ext <| funext fun z => by
    simp [heckeH, Finset.mul_sum, mul_add]

end Hecke

/-! ### The commutation of Hecke operators at distinct primes -/

section Commute

theorem sum_zmod_val {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p] (f : ℕ → M) :
    ∑ b : ZMod p, f b.val = ∑ k ∈ Finset.range p, f k := by
  rw [← Fin.sum_univ_eq_sum_range f p, ← (zmodFin p).sum_comp (fun i => f i)]
  rfl

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (p q : ℕ) (G : ℕ → M) :
    ∑ b ∈ Finset.range p, ∑ c ∈ Finset.range q, G (b + p * c) = ∑ m ∈ Finset.range (q * p), G m := by
  have h1 : ∑ m ∈ Finset.range (q * p), G m = ∑ x : Fin q × Fin p, G (x.2 + p * x.1) := by
    rw [← Fin.sum_univ_eq_sum_range, ← finProdFinEquiv.sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [finProdFinEquiv]
  calc ∑ b ∈ Finset.range p, ∑ c ∈ Finset.range q, G (b + p * c)
      = ∑ b : Fin p, ∑ c : Fin q, G (b + p * c) := by
        rw [← Fin.sum_univ_eq_sum_range (fun b => ∑ c ∈ Finset.range q, G (b + p * c)) p]
        refine Finset.sum_congr rfl fun b _ => ?_
        exact (Fin.sum_univ_eq_sum_range (fun c => G (b + p * c)) q).symm
    _ = ∑ c : Fin q, ∑ b : Fin p, G (b + p * c) := Finset.sum_comm
    _ = ∑ x : Fin q × Fin p, G (x.2 + p * x.1) :=
        (Fintype.sum_prod_type (fun x : Fin q × Fin p => G (x.2 + p * x.1))).symm
    _ = _ := h1.symm

variable {F : ℂ → ℂ} (hper : ∀ w : ℂ, 0 < w.im → F (w + 1) = F w)
include hper

/-- **Reindexing the translates by a unit.** -/
theorem sum_twist (p q : ℕ) [hq : Fact q.Prime] (hpq : ¬ q ∣ p) {z : ℂ} (hz : 0 < z.im) (hp0 : 0 < p) :
    ∑ c : ZMod q, F ((p * z + (c.val : ℂ)) / q) = ∑ c : ZMod q, F (p * ((z + (c.val : ℂ)) / q)) := by
  have hpq' : (p : ZMod q) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulLeft₀ (p : ZMod q) hpq') (fun c => F ((p * z + (c.val : ℂ)) / q))]
  refine Finset.sum_congr rfl fun c _ => ?_
  show F ((p * z + ((((p : ZMod q) * c).val : ℕ) : ℂ)) / q) = F (p * ((z + c.val) / q))
  have hval : ((p : ZMod q) * c).val = p * c.val % q := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hdiv : ((p * c.val : ℕ) : ℂ) = q * ((p * c.val / q : ℕ) : ℂ) + ((p * c.val % q : ℕ) : ℂ) := by
    exact_mod_cast (Nat.div_add_mod (p * c.val) q).symm
  have e : (p : ℂ) * ((z + c.val) / q) = (p * z + ((p * c.val % q : ℕ) : ℂ)) / q + ((p * c.val / q : ℕ) : ℂ) := by
    have h2 : (p : ℂ) * (c.val : ℂ) = ((p * c.val : ℕ) : ℂ) := by push_cast; ring
    field_simp
    rw [mul_add, h2, hdiv]
    ring
  have him : 0 < ((p * z + ((p * c.val % q : ℕ) : ℂ)) / q).im := by
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq.out.pos
    rw [show ((p * z + ((p * c.val % q : ℕ) : ℂ)) / q).im = p * z.im / q by
      simp [Complex.div_natCast_im]]
    positivity
  rw [hval, e, periodic_nat hper him]

omit hper in
/-- **The double sum is a sum over residues modulo `pq`.** -/
theorem sum_double (p q : ℕ) [NeZero p] [NeZero q] (z : ℂ) :
    ∑ b : ZMod p, ∑ c : ZMod q, F (((z + (b.val : ℂ)) / p + (c.val : ℂ)) / q) =
      ∑ c : ZMod q, ∑ b : ZMod p, F (((z + (c.val : ℂ)) / q + (b.val : ℂ)) / p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  set G : ℕ → ℂ := fun m => F ((z + (m : ℂ)) / ((p : ℂ) * q)) with hG
  have hL : ∀ b c : ℕ, F (((z + (b : ℂ)) / p + (c : ℂ)) / q) = G (b + p * c) := by
    intro b c
    simp only [hG]
    congr 1
    push_cast
    field_simp
    ring
  have hR : ∀ c b : ℕ, F (((z + (c : ℂ)) / q + (b : ℂ)) / p) = G (c + q * b) := by
    intro c b
    simp only [hG]
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hL, hR]
  have e1 : ∀ k : ℕ, ∑ c : ZMod q, G (k + p * c.val) = ∑ c ∈ Finset.range q, G (k + p * c) :=
    fun k => sum_zmod_val q (fun c => G (k + p * c))
  have e2 : ∀ k : ℕ, ∑ b : ZMod p, G (k + q * b.val) = ∑ b ∈ Finset.range p, G (k + q * b) :=
    fun k => sum_zmod_val p (fun b => G (k + q * b))
  simp only [e1, e2]
  rw [sum_zmod_val p (fun b => ∑ c ∈ Finset.range q, G (b + p * c)),
    sum_zmod_val q (fun c => ∑ b ∈ Finset.range p, G (c + q * b)), sum_range_mul p q G, sum_range_mul q p G,
    mul_comm]

/-- **`T_p T_q = T_q T_p` for distinct primes**, on `1`-periodic functions of the upper half plane. -/
theorem heckeT_comm (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) {z : ℂ} (hz : 0 < z.im) :
    ∑ i : Option (ZMod p), heckeT q F (heckeAct p i z) = ∑ j : Option (ZMod q), heckeT p F (heckeAct q j z) := by
  have hqp : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp h).symm
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp h)
  simp only [heckeT, Fintype.sum_option, heckeAct, Finset.sum_add_distrib]
  rw [sum_twist hper p q hqp hz hp.out.pos, ← sum_twist hper q p hpq' hz hq.out.pos, sum_double p q z,
    show (q : ℂ) * (p * z) = p * (q * z) by ring]
  ring

end Commute

/-- **The Hecke operators of the cusp channel commute.** -/
theorem heckeH_comm (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) {lam : ℝ}
    {g : UpperHalfPlane → ℂ} (hg : g ∈ cuspSpace lam) :
    heckeH p (heckeH q g) = heckeH q (heckeH p g) := by
  funext z
  rw [heckeH_eq, heckeH_eq]
  unfold heckeT
  have hL : ∑ i : Option (ZMod p), (heckeH q g ∘ ofComplex) (heckeAct p i z) =
      ∑ i : Option (ZMod p), heckeT q (g ∘ ofComplex) (heckeAct p i z) :=
    Finset.sum_congr rfl fun i _ => heckeH_comp_ofComplex q g (heckeAct_im_pos p i z.im_pos)
  have hR : ∑ j : Option (ZMod q), (heckeH p g ∘ ofComplex) (heckeAct q j z) =
      ∑ j : Option (ZMod q), heckeT p (g ∘ ofComplex) (heckeAct q j z) :=
    Finset.sum_congr rfl fun j _ => heckeH_comp_ofComplex p g (heckeAct_im_pos q j z.im_pos)
  rw [hL, hR]
  exact heckeT_comm (periodic_comp hg) p q hpq z.im_pos

/-! ### The Hecke eigenforms -/

/-- The family of Hecke operators on the cusp space, indexed by `ℕ`, identity off the primes. -/
def heckeFamily (lam : ℝ) (n : ℕ) : cuspSpace lam →ₗ[ℂ] cuspSpace lam :=
  if h : n.Prime then (haveI := Fact.mk h; heckeLin n) else LinearMap.id

theorem heckeFamily_comm (lam : ℝ) (m n : ℕ) :
    heckeFamily lam m ∘ₗ heckeFamily lam n = heckeFamily lam n ∘ₗ heckeFamily lam m := by
  unfold heckeFamily
  by_cases hm : m.Prime <;> by_cases hn : n.Prime <;> simp only [hm, hn, dif_pos, dif_neg,
    not_false_eq_true, LinearMap.id_comp, LinearMap.comp_id]
  by_cases hmn : m = n
  · subst hmn
    rfl
  · haveI := Fact.mk hm
    haveI := Fact.mk hn
    refine LinearMap.ext fun g => Subtype.ext ?_
    exact heckeH_comm m n hmn g.2

/-- **Every cusp space of nonzero dimension contains a Hecke eigenform**: a nonzero cusp form that is an
eigenfunction of `T_p` for every prime `p`. -/
theorem exists_heckeEigenform {lam : ℝ} (hS : cuspSpace lam ≠ ⊥) :
    ∃ g ∈ cuspSpace lam, g ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeH p g = c • g := by
  haveI : Nontrivial (cuspSpace lam) := Submodule.nontrivial_iff_ne_bot.mpr hS
  obtain ⟨v, -, hv0, hv⟩ := exists_common_eigenvector (heckeFamily lam) (heckeFamily_comm lam) ⊤
    top_ne_bot fun _ _ _ => trivial
  refine ⟨v.1, v.2, fun h => hv0 (Subtype.ext h), fun p hp => ?_⟩
  obtain ⟨c, hc⟩ := hv p
  refine ⟨c, ?_⟩
  rw [heckeFamily, dif_pos hp.out] at hc
  exact congrArg Subtype.val hc

/-- The component of a basis eigenfunction lies in the cusp space of its eigenvalue. -/
theorem component_mem_cuspSpace (i : CuspEigenIndex 0) :
    (fun z => CuspGravity.cuspFn i z (1 : Deck 0)) ∈ cuspSpace i.1 := by
  have hU := CuspGravity.isCuspLaplaceEigen_cuspFn i
  refine ⟨fun A z => component_smul hU 1 A z, hU.isMaassEigenfunction_component 1,
    tendsto_component_atImInfty hU 1, fun y hy => ?_⟩
  unfold constTerm
  simp only [chart_point]
  exact mean_slice hU 1 hy

theorem cuspSpace_ne_bot (i : CuspEigenIndex 0) : cuspSpace i.1 ≠ ⊥ := by
  intro h
  obtain ⟨w, hw⟩ := CuspGravity.exists_cuspFn_ne_zero i
  have hmem := component_mem_cuspSpace i
  rw [h, Submodule.mem_bot] at hmem
  apply hw
  ext q
  rw [Subsingleton.elim q (1 : Deck 0)]
  exact congrFun hmem w

/-- **Hecke–Maass forms of the modular horizon.** Every eigenvalue of the cusp spectrum carries a nonzero
cusp form that is an eigenfunction of every Hecke operator `T_p`. -/
theorem exists_heckeMaassForm (i : CuspEigenIndex 0) :
    ∃ g : UpperHalfPlane → ℂ, g ≠ 0 ∧ (∀ (A : SL(2, ℤ)) (z : UpperHalfPlane), g (A • z) = g z) ∧
      IsMaassEigenfunction i.1 g ∧ UpperHalfPlane.IsZeroAtImInfty g ∧
      (∀ y : ℝ, 0 < y → constTerm g y = 0) ∧ ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeH p g = c • g := by
  obtain ⟨g, hg, hg0, hH⟩ := exists_heckeEigenform (cuspSpace_ne_bot i)
  exact ⟨g, hg0, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, hH⟩

/-- **Infinitely many Hecke eigenvalue systems**: the set of eigenvalues carrying a Hecke–Maass form is
infinite. -/
theorem infinite_heckeMaass_eigenvalues :
    {lam : ℝ | ∃ g ∈ cuspSpace lam, g ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeH p g = c • g}.Infinite :=
  infinite_cuspEigenvalues.mono fun lam hlam => by
    obtain ⟨i, rfl⟩ := hlam
    exact exists_heckeEigenform (cuspSpace_ne_bot i)

/-- **The trivial Hecke bound**: an eigenvalue of `T_p` on a cusp form has `|c| ≤ p + 1`, i.e. the
normalized eigenvalue `c/√p` lies in `|λ_p| ≤ √p + 1/√p`. -/
theorem norm_heckeEigenvalue_le {lam : ℝ} {g : UpperHalfPlane → ℂ} (hg : g ∈ cuspSpace lam) (hg0 : g ≠ 0)
    (p : ℕ) [hp : Fact p.Prime] {c : ℂ} (hc : heckeH p g = c • g) : ‖c‖ ≤ p + 1 := by
  obtain ⟨C, hC⟩ := exists_bound hg
  have hbdd : BddAbove (Set.range fun z => ‖g z‖) := ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩
  set M := ⨆ z, ‖g z‖ with hM
  have hle : ∀ z, ‖g z‖ ≤ M := fun z => le_ciSup hbdd z
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, g z₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hg0 (funext h)
  have hMpos : 0 < M := lt_of_lt_of_le (norm_pos_iff.mpr hz₀) (hle z₀)
  have hpt : ∀ z, ‖c‖ * ‖g z‖ ≤ (p + 1) * M := by
    intro z
    have h1 := congrFun hc z
    rw [Pi.smul_apply, smul_eq_mul] at h1
    rw [← norm_mul, ← h1, heckeH]
    calc ‖∑ i : Option (ZMod p), g ((alphaQ p i).map (algebraMap ℚ ℝ) • z)‖
        ≤ ∑ i : Option (ZMod p), ‖g ((alphaQ p i).map (algebraMap ℚ ℝ) • z)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Option (ZMod p), M := Finset.sum_le_sum fun i _ => hle _
      _ = (p + 1) * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_option, ZMod.card, nsmul_eq_mul]
          push_cast
          ring
  have hsup : ‖c‖ * M ≤ (p + 1) * M := by
    rw [hM, Real.mul_iSup_of_nonneg (norm_nonneg c)]
    exact ciSup_le hpt
  exact le_of_mul_le_mul_right hsup hMpos

end HeckeCusp

end GaloisForLFunctions.BlackHoleRingdown
