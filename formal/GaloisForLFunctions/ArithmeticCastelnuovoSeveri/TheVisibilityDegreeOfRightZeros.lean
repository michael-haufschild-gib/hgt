import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfAnIsolatedPair
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues
import GaloisForLFunctions.SquareRootThreshold.IntervalSourceTransformsSampledOnLocallyBoundedPoints
import GaloisForLFunctions.RHTower.ZetaWeilFiniteLevelInertia

/-!
# The visibility degree of `n` right zeros

How large a degree `a` is needed for `n` zeros right of the critical line (`Re ρ > ½`) to become
visible in the degree filtration `hodgeDefectAt Z a` of the Hodge defect?

* **Over `𝔽_q` (`negIndex_spanGram_eq_of_onCircle`).** For a curve datum `D` the spectrum splits
  into `onCircleSpectrum` (`|β| = 1`), `outerSpectrum` (`|β| > 1`), and its circle reflection
  `innerSpectrum` (`|β| < 1`). Once the Frobenius window reaches
  `m ≥ |onCircleSpectrum| + 2 |outerSpectrum|`, Lagrange interpolation separates all outer pairs
  from the on-circle background and `hermNegIndex (D.spanGram m) = |outerSpectrum|`.
* **Exact `n`-pair law and hiding in an on-line lattice (`W_multiPairConfig`,
  `hodgeDefectAt_multiPairConfig_le`, `exists_n_hidden_at_degree`).** Inserting `n` distinct
  off-line pairs `½ ± δ_k + iγ_k` into the doubled on-line lattice of spacing `2π/L` gives a
  tempered configuration with `(rightZeros Z).encard = n`. Below the Nyquist degree `a ≤ L/2`,
  Poisson summation collapses the infinite on-line background to `2L‖f‖²` and gives the exact
  identity
  `Re W(f, f) = 2L ∫ ‖f‖² + ½ Σ_k (‖h_f(γ_k − iδ_k) + h_f(γ_k + iδ_k)‖² − ‖h_f(γ_k − iδ_k) − h_f(γ_k + iδ_k)‖²)`.
  Whenever the pair energies outside a subset `S` satisfy `Σ_{k ∉ S} (sinh(2δ_k a)/(2δ_k) − a) ≤ L`,
  the form is nonnegative on the `|S|` node conditions `h_f(γ_k − iδ_k) = h_f(γ_k + iδ_k)` (`k ∈ S`),
  so `hodgeDefectAt Z a ≤ |S|`. In particular `hodgeDefectAt Z a = 0` while
  `Σ_k (sinh(2δ_k a)/(2δ_k) − a) ≤ L`, and for every `n`, degree `a > 0`, and depth `δ ∈ (0, ½]`
  there is a tempered configuration with `n` right zeros and `hodgeDefectAt Z a = 0`.
* **Explicit visibility degree from on-line mass and local density (`hodgeDefectAt_eq_of_onLineMass`,
  `hodgeDefectAt_eq_of_log_onLineMass`, `hodgeDefectAt_multiPairConfig_eq_card`,
  `hodgeDefectAt_eq_of_locallyBounded`).** For any tempered configuration `Z` with finite right-zero
  set `R` and dual tests `b_ρ` supported in `[−a₀, a₀]` (which exist for every `a₀ > 0` by
  `exists_dual_tests_Icc`), only the on-line zeros `Re τ = ½` oppose the phased translates
  `b_ρ + ω_ρ b_ρ(· − Δ)`. Once `2 A_on + ½ ≤ cosh((Re ρ − ½)Δ) − 1` for all `ρ ∈ R` (in particular
  for `Δ ≥ log(4 A_on + 3)/(Re ρ − ½)`), where `A_on = Σ_{Re τ = ½} m_τ Σ_ρ |h_{b_ρ}(γ_τ)|²`,
  every degree `a ≥ a₀ + Δ` achieves full visibility `hodgeDefectAt Z a = |R|`. On `multiPairConfig`
  with `a₀ ≤ L/2`, Poisson summation gives the exact identity `A_on = 2L Σ_ρ ∫ ‖b_ρ‖²`; on any
  configuration with at most `M` on-line zeros of multiplicity `≤ m₀` per unit-radius window,
  sampling bounds `A_on ≤ m₀ M (2a₀ + 2π) e^{2π} Σ_ρ ∫ ‖b_ρ‖²`.
* **Separated right zeros under logarithmic local density and the scaling surface of `ℤ`
  (`card_le_hodgeDefectAt_of_visible_pairs`, `zeta_intersectionGram_posIndex_ge_of_visible_pairs`).**
  Under `N(t, t+1] ≤ A₀ log(|t| + 3)`, any finite set `T` of separated isolated right zeros with
  `visibleMargin A₀ a δ R Hm > 0` gives `(|T| : ℕ∞) ≤ hodgeDefectAt Z a` without finiteness of
  `rightZeros Z`, and for `ζ` yields `1 + |T|` positive squares of `intersectionGram Λ` at degree `a`.
-/

open Complex MeasureTheory Set Filter Topology Finset Matrix
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig offLinePoint pairEnergy
  pairEnergy_nonneg norm_sub_sq_le_pairEnergy hasSum_Wsummand_onLineLattice
  hasSum_lattice_weight integral_mul_conj_self_eq eq_zero_of_not_mem_Icc
  temperedConfig_zetaZeroConfig summable_tsum_norm_sq_testTransform_le_of_locallyBounded)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Calibration over `𝔽_q`: visibility degree in terms of the on-circle spectrum -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The distinct normalized Frobenius eigenvalues on the critical circle `|β| = 1`. -/
def onCircleSpectrum : Finset ℂ := D.spectrum.filter fun z => ‖z‖ = 1

/-- The distinct normalized Frobenius eigenvalues inside the critical circle `|β| < 1`. -/
def innerSpectrum : Finset ℂ := D.spectrum.filter fun z => ‖z‖ < 1

theorem circleReflect_mem_spectrum {z : ℂ} (hz : z ∈ D.spectrum) :
    circleReflect z ∈ D.spectrum := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  rw [← D.β_reflPerm]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- Circle reflection bijects the inner spectrum onto the outer spectrum. -/
theorem card_innerSpectrum_eq_card_outerSpectrum :
    D.innerSpectrum.card = D.outerSpectrum.card := by
  refine Finset.card_bij (fun z _ => circleReflect z) (fun z hz => ?_) (fun z₁ _ z₂ _ h => ?_)
    (fun w hw => ?_)
  · obtain ⟨hzs, hz1⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hzs
    refine Finset.mem_filter.mpr ⟨D.circleReflect_mem_spectrum hzs, ?_⟩
    rw [norm_circleReflect]
    exact one_lt_inv₀ (norm_pos_iff.mpr (D.β_ne_zero i)) |>.mpr hz1
  · have := congrArg circleReflect h
    simpa [circleReflect_circleReflect] using this
  · obtain ⟨hws, hw1⟩ := Finset.mem_filter.mp hw
    refine ⟨circleReflect w, Finset.mem_filter.mpr ⟨D.circleReflect_mem_spectrum hws, ?_⟩,
      circleReflect_circleReflect _⟩
    rw [norm_circleReflect]
    exact inv_lt_one_of_one_lt₀ hw1

/-- The spectrum partitions into the on-circle eigenvalues and the reflected outer/inner pairs:
`|spectrum| = |onCircleSpectrum| + 2 |outerSpectrum|`. -/
theorem card_spectrum_eq_onCircle_add_two_mul_outer :
    D.spectrum.card = D.onCircleSpectrum.card + 2 * D.outerSpectrum.card := by
  have h1 : D.spectrum.card =
      (D.spectrum.filter fun z => ‖z‖ = 1).card + (D.spectrum.filter fun z => ¬‖z‖ = 1).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have h2 : (D.spectrum.filter fun z => ¬‖z‖ = 1) = D.outerSpectrum ∪ D.innerSpectrum := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_union, outerSpectrum, innerSpectrum]
    constructor
    · rintro ⟨hz, hne⟩
      rcases lt_trichotomy ‖z‖ 1 with h | h | h
      · exact Or.inr ⟨hz, h⟩
      · exact absurd h hne
      · exact Or.inl ⟨hz, h⟩
    · rintro (⟨hz, h⟩ | ⟨hz, h⟩)
      · exact ⟨hz, ne_of_gt h⟩
      · exact ⟨hz, ne_of_lt h⟩
  have hdisj : Disjoint D.outerSpectrum D.innerSpectrum := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have hgt := (Finset.mem_filter.mp hz1).2
    have hlt := (Finset.mem_filter.mp hz2).2
    linarith
  rw [h1, h2, Finset.card_union_of_disjoint hdisj, D.card_innerSpectrum_eq_card_outerSpectrum,
    onCircleSpectrum]
  ring

/-- **Visibility degree over `𝔽_q`.** All `n = |outerSpectrum|` outer eigenvalues become visible in
the Frobenius span Gram matrix as soon as the window degree reaches `|onCircleSpectrum| + 2n`. -/
theorem negIndex_spanGram_eq_of_onCircle {m : ℕ}
    (hm : D.onCircleSpectrum.card + 2 * D.outerSpectrum.card ≤ m) :
    hermNegIndex (D.spanGram m) = D.outerSpectrum.card :=
  D.negIndex_spanGram_eq (D.card_spectrum_eq_onCircle_add_two_mul_outer.trans_le hm)

end CurveDatum

/-! ### 2. Exact `n`-pair law and degree filtration in an on-line lattice of density `L` -/

section MultiPair

variable {L : ℝ} (hL : 0 < L) {n : ℕ} (δ γ : Fin n → ℝ)
  (hδ : ∀ k, 0 < δ k) (hδ' : ∀ k, δ k ≤ 1 / 2)

/-- The doubled on-line lattice of spacing `2π/L` together with `n` off-line pairs
`½ ± δ_k + iγ_k`. -/
def multiPairConfig : ZeroConfig where
  carrier := (Set.range (RHTower.verticalLatticePoint L 0) ∪
      Set.range fun k : Fin n => offLinePoint (δ k) (γ k)) ∪
    Set.range fun k : Fin n => offLinePoint (-δ k) (γ k)
  mult := fun ρ => if ρ.re = 1 / 2 then 2 else 1
  one_le_mult := fun _ _ => by split_ifs <;> norm_num
  strip := by
    rintro _ ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩)
    · simp only [RHTower.verticalLatticePoint]; constructor <;> norm_num
    · simp only [offLinePoint]; constructor <;> linarith [hδ k, hδ' k]
    · simp only [offLinePoint]; constructor <;> linarith [hδ k, hδ' k]
  reflect_mem := by
    rintro _ ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩)
    · exact Or.inl (Or.inl ⟨k, by
        rw [RHTower.reflect_verticalLatticePoint, neg_zero]⟩)
    · exact Or.inr ⟨k, (SquareRootThreshold.reflect_offLinePoint (δ k) (γ k)).symm⟩
    · exact Or.inl (Or.inr ⟨k, by
        rw [SquareRootThreshold.reflect_offLinePoint, neg_neg]⟩)
  mult_reflect := by
    intro ρ _
    have hre : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    simp only [hre]
    by_cases h : ρ.re = 1 / 2
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (fun h' => h (by linarith))]
  finite_window := by
    intro T₁ T₂
    have hF := RHTower.finite_latticeWindow (h := 2 * π / L) (by positivity) T₁ T₂
    refine (((hF.image (RHTower.verticalLatticePoint L 0)).union
      (Set.finite_range fun k : Fin n => offLinePoint (δ k) (γ k))).union
        (Set.finite_range fun k : Fin n => offLinePoint (-δ k) (γ k))).subset ?_
    rintro _ ⟨((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩), h1, h2⟩
    · exact Or.inl (Or.inl ⟨k, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨k, rfl⟩)
    · exact Or.inr ⟨k, rfl⟩

include hδ in
theorem disjoint_onLine_offLine_pos (L : ℝ) :
    Disjoint (Set.range (RHTower.verticalLatticePoint L 0))
      (Set.range fun k : Fin n => offLinePoint (δ k) (γ k)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨m, rfl⟩ ⟨k, hk⟩
  have := congrArg Complex.re hk
  simp only [RHTower.verticalLatticePoint, offLinePoint] at this
  linarith [hδ k]

include hδ in
theorem disjoint_onLine_pos_offLine_neg (L : ℝ) :
    Disjoint (Set.range (RHTower.verticalLatticePoint L 0) ∪
        Set.range fun k : Fin n => offLinePoint (δ k) (γ k))
      (Set.range fun k : Fin n => offLinePoint (-δ k) (γ k)) := by
  rw [Set.disjoint_left]
  rintro _ (⟨m, rfl⟩ | ⟨k, rfl⟩) ⟨j, hj⟩
  · have := congrArg Complex.re hj
    simp only [RHTower.verticalLatticePoint, offLinePoint] at this
    linarith [hδ j]
  · have := congrArg Complex.re hj
    simp only [offLinePoint] at this
    linarith [hδ k, hδ j]

theorem injective_offLinePoint_neg_of_pos
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k)) :
    Function.Injective fun k : Fin n => offLinePoint (-δ k) (γ k) := by
  intro k j h
  apply hinj
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [offLinePoint] at hre him
  apply Complex.ext <;> simp only [offLinePoint] <;> linarith

/-- The `n`-pair lattice configuration is tempered. -/
theorem temperedConfig_multiPairConfig :
    TemperedConfig (multiPairConfig hL δ γ hδ hδ') := by
  classical
  set Z := multiPairConfig hL δ γ hδ hδ'
  set G : ℂ → ℝ := fun ρ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hG
  obtain ⟨a, ha⟩ := hasSum_lattice_weight hL 0 2
  have hmult : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else 1 := fun _ => rfl
  have ha' : HasSum (fun ρ : Set.range (RHTower.verticalLatticePoint L 0) => G ρ) a := by
    convert ha using 2 with ρ
    obtain ⟨_, m, rfl⟩ := ρ
    simp only [hG, hmult, RHTower.verticalLatticePoint, add_zero, if_true, Nat.cast_ofNat]
  haveI : Fintype (Set.range fun k : Fin n => offLinePoint (δ k) (γ k)) := Fintype.ofFinite _
  haveI : Fintype (Set.range fun k : Fin n => offLinePoint (-δ k) (γ k)) := Fintype.ofFinite _
  exact ⟨_, HasSum.add_disjoint (f := G) (disjoint_onLine_pos_offLine_neg δ γ hδ L)
    (HasSum.add_disjoint (f := G) (disjoint_onLine_offLine_pos δ γ hδ L) ha' (hasSum_fintype _))
    (hasSum_fintype _)⟩

/-- The zeros of `multiPairConfig` right of the critical line are the `n` points
`½ + δ_k + iγ_k`. -/
theorem rightZeros_multiPairConfig :
    rightZeros (multiPairConfig hL δ γ hδ hδ') =
      Set.range fun k : Fin n => offLinePoint (δ k) (γ k) := by
  ext ρ
  simp only [rightZeros, multiPairConfig, Set.mem_setOf_eq, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨((⟨m, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩), hre⟩
    · simp [RHTower.verticalLatticePoint] at hre
    · exact ⟨k, rfl⟩
    · simp only [offLinePoint] at hre
      linarith [hδ k]
  · rintro ⟨k, rfl⟩
    exact ⟨Or.inl (Or.inr ⟨k, rfl⟩), by simp only [offLinePoint]; linarith [hδ k]⟩

theorem encard_rightZeros_multiPairConfig
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k)) :
    (rightZeros (multiPairConfig hL δ γ hδ hδ')).encard = n := by
  rw [rightZeros_multiPairConfig, ← Set.image_univ, hinj.encard_image,
    Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

/-- The total Hodge defect of the `n`-pair configuration is `n`. -/
theorem iSup_hodgeDefectAt_multiPairConfig
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k)) :
    ⨆ a, hodgeDefectAt (multiPairConfig hL δ γ hδ hδ') a = n := by
  rw [iSup_hodgeDefectAt _ (temperedConfig_multiPairConfig hL δ γ hδ hδ'),
    encard_rightZeros_multiPairConfig hL δ γ hδ hδ' hinj]

/-- **The `n`-pair Weil form identity.** Below the Nyquist degree `L/2`, the infinite on-line
lattice sums by Poisson summation to `2L‖f‖²` and each off-line pair adds its reflected transform
product. -/
theorem W_multiPairConfig
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (multiPairConfig hL δ γ hδ hδ').W f f =
      2 * L * (∫ t, f t * conj (f t)) +
        ∑ k : Fin n,
          (paperFT f ((γ k : ℂ) - I * δ k) * conj (paperFT f ((γ k : ℂ) + I * δ k)) +
            paperFT f ((γ k : ℂ) + I * δ k) * conj (paperFT f ((γ k : ℂ) - I * δ k))) := by
  set Z := multiPairConfig hL δ γ hδ hδ'
  have hmultdef : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else 1 := fun _ => rfl
  have hmult : ∀ m : ℤ, Z.mult (RHTower.verticalLatticePoint L 0 m) = 2 := fun m => by
    rw [hmultdef, if_pos (by simp [RHTower.verticalLatticePoint])]
  have h₁ := hasSum_Wsummand_onLineLattice Z hL hmult hf hf.continuous hfs hfs
  have hvp : ∀ k : Fin n, Z.Wsummand f f (offLinePoint (δ k) (γ k)) =
      paperFT f ((γ k : ℂ) - I * δ k) * conj (paperFT f ((γ k : ℂ) + I * δ k)) := fun k => by
    have hm : Z.mult (offLinePoint (δ k) (γ k)) = 1 := by
      rw [hmultdef, if_neg]; simp only [offLinePoint]; linarith [hδ k]
    have hconj : conj ((γ k : ℂ) - I * δ k) = (γ k : ℂ) + I * δ k := by
      simp [map_sub, Complex.conj_ofReal, Complex.conj_I]
    unfold ZeroConfig.Wsummand
    rw [hm, SquareRootThreshold.gammaOf_offLinePoint, hconj]
    simp
  have hvq : ∀ k : Fin n, Z.Wsummand f f (offLinePoint (-δ k) (γ k)) =
      paperFT f ((γ k : ℂ) + I * δ k) * conj (paperFT f ((γ k : ℂ) - I * δ k)) := fun k => by
    have hm : Z.mult (offLinePoint (-δ k) (γ k)) = 1 := by
      rw [hmultdef, if_neg]; simp only [offLinePoint]; linarith [hδ k]
    have hconj : conj ((γ k : ℂ) + I * δ k) = (γ k : ℂ) - I * δ k := by
      simp [map_add, Complex.conj_ofReal, Complex.conj_I]; ring
    unfold ZeroConfig.Wsummand
    rw [hm, SquareRootThreshold.gammaOf_offLinePoint]
    push_cast
    rw [show (γ k : ℂ) - I * -(δ k : ℂ) = (γ k : ℂ) + I * δ k by ring, hconj]
    simp
  have hp : HasSum (fun ρ : Set.range (fun k : Fin n => offLinePoint (δ k) (γ k)) =>
      Z.Wsummand f f ρ)
      (∑ k : Fin n, paperFT f ((γ k : ℂ) - I * δ k) * conj (paperFT f ((γ k : ℂ) + I * δ k))) := by
    rw [hinj.hasSum_range_iff]
    simpa [Function.comp_def, hvp] using
      hasSum_fintype (fun k : Fin n => Z.Wsummand f f (offLinePoint (δ k) (γ k)))
  have hinj' := injective_offLinePoint_neg_of_pos δ γ hinj
  have hq : HasSum (fun ρ : Set.range (fun k : Fin n => offLinePoint (-δ k) (γ k)) =>
      Z.Wsummand f f ρ)
      (∑ k : Fin n, paperFT f ((γ k : ℂ) + I * δ k) * conj (paperFT f ((γ k : ℂ) - I * δ k))) := by
    rw [hinj'.hasSum_range_iff]
    simpa [Function.comp_def, hvq] using
      hasSum_fintype (fun k : Fin n => Z.Wsummand f f (offLinePoint (-δ k) (γ k)))
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) (disjoint_onLine_pos_offLine_neg δ γ hδ L)
    (HasSum.add_disjoint (f := Z.Wsummand f f) (disjoint_onLine_offLine_pos δ γ hδ L) h₁ hp) hq
  rw [ZeroConfig.W]
  refine hall.tsum_eq.trans ?_
  rw [add_assoc, ← Finset.sum_add_distrib]

/-- Polarization of a reflected pair product into its even and odd squares. -/
theorem re_pair_eq_half_norm_add_sq_sub_norm_sub_sq (A B : ℂ) :
    (A * conj B + B * conj A).re = (‖A + B‖ ^ 2 - ‖A - B‖ ^ 2) / 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Real `n`-pair Weil form identity.** Below `L/2`, the real Weil form decomposes into the
on-line energy `2L‖f‖²`, the positive even pair squares `½‖h_f(γ_k − iδ_k) + h_f(γ_k + iδ_k)‖²`,
and the negative odd pair squares `−½‖h_f(γ_k − iδ_k) − h_f(γ_k + iδ_k)‖²`. -/
theorem re_W_multiPairConfig
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    ((multiPairConfig hL δ γ hδ hδ').W f f).re =
      2 * L * (∫ t, ‖f t‖ ^ 2) +
        ∑ k : Fin n,
          (‖paperFT f ((γ k : ℂ) - I * δ k) + paperFT f ((γ k : ℂ) + I * δ k)‖ ^ 2 -
            ‖paperFT f ((γ k : ℂ) - I * δ k) - paperFT f ((γ k : ℂ) + I * δ k)‖ ^ 2) / 2 := by
  rw [W_multiPairConfig hL δ γ hδ hδ' hinj hf hfs, integral_mul_conj_self_eq, Complex.add_re,
    Complex.re_sum]
  have hre : (2 * (L : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)).re = 2 * L * ∫ t, ‖f t‖ ^ 2 := by
    rw [show (2 * (L : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) =
      ((2 * L * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [hre]
  congr 1
  exact Finset.sum_congr rfl fun k _ => re_pair_eq_half_norm_add_sq_sub_norm_sub_sq _ _

/-- **Node lower bound for `n` pairs.** If a test supported in `[−a, a]` (`a ≤ L/2`) satisfies the
node condition `h_f(γ_k − iδ_k) = h_f(γ_k + iδ_k)` on `S ⊆ Fin n`, only the pairs outside `S`
contribute negative energy:
`Re W(f, f) ≥ 2 (L − Σ_{k ∉ S} pairEnergy(δ_k, a)) ∫ ‖f‖²`. -/
theorem re_W_multiPairConfig_ge_of_nodes
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k))
    (S : Finset (Fin n)) {a : ℝ} (ha : 0 ≤ a) (haL : a ≤ L / 2) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hnode : ∀ k ∈ S, paperFT f ((γ k : ℂ) - I * δ k) = paperFT f ((γ k : ℂ) + I * δ k)) :
    2 * (L - ∑ k ∈ Sᶜ, pairEnergy (δ k) a) * (∫ t, ‖f t‖ ^ 2) ≤
      ((multiPairConfig hL δ γ hδ hδ').W f f).re := by
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Set.Icc_subset_Icc (by linarith) haL)
  rw [re_W_multiPairConfig hL δ γ hδ hδ' hinj hf hfs']
  have hterm : ∀ k : Fin n,
      (if k ∈ Sᶜ then -(2 * pairEnergy (δ k) a * ∫ t, ‖f t‖ ^ 2) else 0) ≤
        (‖paperFT f ((γ k : ℂ) - I * δ k) + paperFT f ((γ k : ℂ) + I * δ k)‖ ^ 2 -
          ‖paperFT f ((γ k : ℂ) - I * δ k) - paperFT f ((γ k : ℂ) + I * δ k)‖ ^ 2) / 2 := by
    intro k
    by_cases hk : k ∈ S
    · have hkc : k ∉ Sᶜ := by simp [hk]
      rw [if_neg hkc, hnode k hk, sub_self, norm_zero]
      have : 0 ≤ ‖paperFT f ((γ k : ℂ) + I * δ k) + paperFT f ((γ k : ℂ) + I * δ k)‖ ^ 2 :=
        sq_nonneg _
      linarith
    · have hkc : k ∈ Sᶜ := Finset.mem_compl.mpr hk
      rw [if_pos hkc]
      have : 0 ≤ ‖paperFT f ((γ k : ℂ) - I * δ k) + paperFT f ((γ k : ℂ) + I * δ k)‖ ^ 2 :=
        sq_nonneg _
      have hsub := norm_sub_sq_le_pairEnergy (hδ k) ha (γ k) hf.continuous hfs
      linarith
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm k
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_neg_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum] at hsum
  linarith

/-- **Stepwise degree filtration bound.** If the pairs outside `S ⊆ Fin n` have collective pair
energy at most `L` at degree `a ≤ L/2`, the Hodge defect at degree `a` is at most `|S|`. -/
theorem hodgeDefectAt_multiPairConfig_le
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k))
    (S : Finset (Fin n)) {a : ℝ} (ha : 0 ≤ a) (haL : a ≤ L / 2)
    (hE : ∑ k ∈ Sᶜ, pairEnergy (δ k) a ≤ L) :
    hodgeDefectAt (multiPairConfig hL δ γ hδ hδ') a ≤ S.card := by
  classical
  set Z := multiPairConfig hL δ γ hδ hδ'
  have hZ := temperedConfig_multiPairConfig hL δ γ hδ hδ'
  refine iSup₂_le fun m f => iSup_le fun hf => ?_
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hf i).2
  set Lmap : S → (Fin m → ℂ) →ₗ[ℂ] ℂ := fun k =>
    evalFunctional f ((γ k : ℂ) - I * δ k) - evalFunctional f ((γ k : ℂ) + I * δ k)
  refine (ENat.coe_le_coe.mpr (negIndex_le_card_of_nonneg_on_ker _ Lmap fun x hx => ?_)).trans_eq
    (by simp)
  rw [hermQuad_zeroGram_of_tempered Z hZ f (fun i => (hf i).1) hfc]
  set F : ℝ → ℂ := ∑ i, conj (x i) • f i
  have hFd : ContDiff ℝ 2 F := contDiff_sum_smul f (fun i => (hf i).1) _
  have hFs : tsupport F ⊆ Icc (-a) a := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra hout
    apply hu
    simp only [F, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : f i u = 0 := image_eq_zero_of_notMem_tsupport fun h => hout ((hf i).2 h)
    simp [this]
  have hnode : ∀ k ∈ S, paperFT F ((γ k : ℂ) - I * δ k) = paperFT F ((γ k : ℂ) + I * δ k) := by
    intro k hk
    have h0 := hx ⟨k, hk⟩
    simp only [Lmap, LinearMap.sub_apply, evalFunctional_eq f (fun i => (hf i).1.continuous) hfc,
      sub_eq_zero] at h0
    exact (starRingEnd ℂ).injective h0
  have hge := re_W_multiPairConfig_ge_of_nodes hL δ γ hδ hδ' hinj S ha haL hFd hFs hnode
  have hI : 0 ≤ ∫ t, ‖F t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hL0 : 0 ≤ 2 * (L - ∑ k ∈ Sᶜ, pairEnergy (δ k) a) := by linarith
  exact le_trans (mul_nonneg hL0 hI) hge

/-- **Collective invisibility of `n` pairs.** Below `L/2`, while the sum of the `n` pair energies
`sinh(2δ_k a)/(2δ_k) − a` is at most the background density `L`, the Hodge defect vanishes. -/
theorem hodgeDefectAt_multiPairConfig_eq_zero
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k))
    {a : ℝ} (ha : 0 ≤ a) (haL : a ≤ L / 2)
    (hE : ∑ k : Fin n, pairEnergy (δ k) a ≤ L) :
    hodgeDefectAt (multiPairConfig hL δ γ hδ hδ') a = 0 := by
  have h := hodgeDefectAt_multiPairConfig_le hL δ γ hδ hδ' hinj ∅ ha haL (by simpa using hE)
  simpa using h

end MultiPair

/-- **Impossibility of a uniform visibility degree for `n` right zeros.** For every `n : ℕ`,
every degree `a > 0`, and every depth `δ ∈ (0, ½]`, there is a tempered configuration with
`n` zeros right of the critical line whose Hodge defect vanishes at degree `a`. -/
theorem exists_n_hidden_at_degree (n : ℕ) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (rightZeros Z).encard = n ∧ hodgeDefectAt Z a = 0 := by
  set L : ℝ := max (2 * a) (n * pairEnergy δ a)
  have hL : 0 < L := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set d : Fin n → ℝ := fun _ => δ
  set g : Fin n → ℝ := fun k => (k : ℕ)
  have hinj : Function.Injective fun k : Fin n => offLinePoint (d k) (g k) := by
    intro k j h
    have him := congrArg Complex.im h
    simp only [offLinePoint, g] at him
    exact Fin.ext (Nat.cast_injective him)
  refine ⟨multiPairConfig hL d g (fun _ => hδ) (fun _ => hδ'),
    temperedConfig_multiPairConfig hL d g (fun _ => hδ) (fun _ => hδ'),
    encard_rightZeros_multiPairConfig hL d g (fun _ => hδ) (fun _ => hδ') hinj, ?_⟩
  refine hodgeDefectAt_multiPairConfig_eq_zero hL d g (fun _ => hδ) (fun _ => hδ') hinj ha.le ?_ ?_
  · have := le_max_left (2 * a) (n * pairEnergy δ a); linarith
  · simp only [d, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_max_right _ _

/-! ### 3. Explicit visibility degree from on-line mass and local density -/

/-- The zero-side summand of a family `b` restricted to the critical line `Re τ = ½`. -/
def onLineSummand (Z : ZeroConfig) {R : Type*} [Fintype R] (b : R → ℝ → ℂ) (τ : Z.carrier) : ℝ :=
  if (τ : ℂ).re = 1 / 2 then ∑ ρ, (Z.mult τ : ℝ) * ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2 else 0

/-- The total on-line zero mass `Σ_{Re τ = ½} m_τ Σ_ρ |h_{b_ρ}(γ_τ)|²` of a test family `b`. -/
def onLineMass (Z : ZeroConfig) {R : Type*} [Fintype R] (b : R → ℝ → ℂ) : ℝ :=
  ∑' τ : Z.carrier, onLineSummand Z b τ

theorem onLineSummand_nonneg (Z : ZeroConfig) {R : Type*} [Fintype R] (b : R → ℝ → ℂ)
    (τ : Z.carrier) : 0 ≤ onLineSummand Z b τ := by
  unfold onLineSummand
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by positivity
  · exact le_refl 0

theorem onLineMass_nonneg (Z : ZeroConfig) {R : Type*} [Fintype R] (b : R → ℝ → ℂ) :
    0 ≤ onLineMass Z b :=
  tsum_nonneg (onLineSummand_nonneg Z b)

theorem summable_onLineSummand (Z : ZeroConfig) (hZ : TemperedConfig Z) {R : Type*} [Fintype R]
    {b : R → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ)) (hbc : ∀ ρ, HasCompactSupport (b ρ)) :
    Summable (onLineSummand Z b) := by
  have hS : Summable fun τ : Z.carrier =>
      ∑ ρ, (Z.mult τ : ℝ) * ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2 :=
    summable_sum fun ρ _ => (summable_mult_norm_mul Z hZ (hb ρ) (hbc ρ) (hb ρ) (hbc ρ)
      (fun τ => gammaOf τ) (abs_im_gammaOf_le Z)).congr fun τ => by ring
  refine Summable.of_nonneg_of_le (onLineSummand_nonneg Z b) (fun τ => ?_) hS
  unfold onLineSummand
  split_ifs
  · exact le_refl _
  · exact Finset.sum_nonneg fun _ _ => by positivity

theorem one_sub_exp_mul_one_sub_exp_neg (x : ℝ) :
    (1 - Real.exp x) * (1 - Real.exp (-x)) = -2 * (Real.cosh x - 1) := by
  rw [Real.cosh_eq]
  have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  linarith

/-- **Hyperbolic negativity of phased dual pairs.** Only the on-line zeros `Re τ = ½` oppose the
phased translates of a dual family `b`: once `2 · onLineMass Z b + ½ ≤ cosh((Re ρ − ½)Δ) − 1` for
all `ρ ∈ R`, the Weil form of `Σ_ρ conj(y_ρ)(b_ρ + ω_ρ b_ρ(· − Δ))` is at most `−Σ_ρ |y_ρ|²`. -/
theorem re_W_pairComb_le_of_onLineMass (Z : ZeroConfig) (hZ : TemperedConfig Z) {R : Finset ℂ}
    (hRm : ∀ ρ : R, (ρ : ℂ) ∈ Z.carrier ∧ 1 / 2 < (ρ : ℂ).re)
    (hRall : ∀ τ ∈ Z.carrier, 1 / 2 < τ.re → τ ∈ R)
    {b : R → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ)) (hbc : ∀ ρ, HasCompactSupport (b ρ))
    (hb1 : ∀ ρ σ : R, paperFT (b ρ) (gammaOf σ) = if σ = ρ then 1 else 0)
    (hb2 : ∀ ρ σ : R, paperFT (b ρ) (conj (gammaOf σ)) = if σ = ρ then 1 else 0)
    {Δ : ℝ} (hΔ : ∀ ρ : R, 2 * onLineMass Z b + 1 / 2 ≤ Real.cosh (((ρ : ℂ).re - 1 / 2) * Δ) - 1)
    (y : R → ℂ) :
    (Z.W (∑ p : R × Fin 2, conj (y p.1) • pairFamily b (fun ρ => phase Δ ρ) Δ p)
      (∑ p : R × Fin 2, conj (y p.1) • pairFamily b (fun ρ => phase Δ ρ) Δ p)).re ≤
      -∑ ρ, ‖y ρ‖ ^ 2 := by
  classical
  set F := ∑ p : R × Fin 2, conj (y p.1) • pairFamily b (fun ρ => phase Δ ρ) Δ p with hF
  have hFd : ContDiff ℝ 2 F := contDiff_sum_smul _ (pairFamily_contDiff hb _ Δ) _
  have hFc : HasCompactSupport F :=
    hasCompactSupport_sum_smul _ (pairFamily_hasCompactSupport hbc _ Δ) _
  have hS : Summable (onLineSummand Z b) := summable_onLineSummand Z hZ hb hbc
  set A := onLineMass Z b with hAdef
  have hA0 : 0 ≤ A := onLineMass_nonneg Z b
  set Y := ∑ ρ, ‖y ρ‖ ^ 2 with hYdef
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun ρ _ => by positivity
  set δ : R → ℝ := fun ρ => (ρ : ℂ).re - 1 / 2 with hδdef
  set v : R → ℝ := fun ρ => (Z.mult ρ : ℝ) * ‖y ρ‖ ^ 2 *
    ((1 - Real.exp (δ ρ * Δ)) * (1 - Real.exp (-(δ ρ * Δ)))) with hvdef
  have hright : ∀ ρ : R, Z.Wsummand F F ρ = (v ρ : ℂ) := fun ρ => by
    refine Wsummand_eq_of_values Z F ρ (y ρ) _ _ ?_ ?_
    · rw [hF, paperFT_pairComb_of_dual hb hbc _ Δ y fun σ => hb1 σ ρ, phase_mul_cexp_gammaOf,
        ← sub_eq_add_neg]
    · rw [hF, paperFT_pairComb_of_dual hb hbc _ Δ y fun σ => hb2 σ ρ,
        phase_mul_cexp_conj_gammaOf, ← sub_eq_add_neg]
  have hv : ∀ ρ : R, v ρ ≤ ‖y ρ‖ ^ 2 * (-4 * A - 1) := fun ρ => by
    have hΔρ : 2 * A + 1 / 2 ≤ Real.cosh (δ ρ * Δ) - 1 := hΔ ρ
    have hP : (1 - Real.exp (δ ρ * Δ)) * (1 - Real.exp (-(δ ρ * Δ))) ≤ -4 * A - 1 := by
      rw [one_sub_exp_mul_one_sub_exp_neg]
      linarith
    have hP0 : (1 - Real.exp (δ ρ * Δ)) * (1 - Real.exp (-(δ ρ * Δ))) ≤ 0 := by linarith
    have hm : (1 : ℝ) ≤ Z.mult ρ := by exact_mod_cast Z.one_le_mult _ (hRm ρ).1
    have hmP : (Z.mult ρ : ℝ) * ((1 - Real.exp (δ ρ * Δ)) * (1 - Real.exp (-(δ ρ * Δ)))) ≤
        -4 * A - 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) (neg_nonneg.mpr hP0)]
    calc v ρ = ‖y ρ‖ ^ 2 * ((Z.mult ρ : ℝ) *
          ((1 - Real.exp (δ ρ * Δ)) * (1 - Real.exp (-(δ ρ * Δ))))) := by
          simp only [hvdef]; ring
      _ ≤ ‖y ρ‖ ^ 2 * (-4 * A - 1) := mul_le_mul_of_nonneg_left hmP (by positivity)
  have hv0 : ∀ ρ : R, v ρ ≤ 0 := fun ρ =>
    (hv ρ).trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
  set ι : R → Z.carrier := fun ρ => ⟨ρ, (hRm ρ).1⟩ with hιdef
  set E : Z.carrier → ℝ := fun τ => ∑ ρ, if τ = ι ρ then v ρ else 0 with hEdef
  have hE0 : ∀ τ : Z.carrier, (τ : ℂ).re ≤ 1 / 2 → E τ = 0 := fun τ hτ =>
    Finset.sum_eq_zero fun ρ _ => if_neg fun h => by
      have : (τ : ℂ) = ρ := congrArg Subtype.val h
      linarith [(hRm ρ).2, congrArg Complex.re this]
  have hpt : ∀ τ : Z.carrier, (Z.Wsummand F F τ).re ≤ 4 * Y * onLineSummand Z b τ + E τ := by
    intro τ
    rcases lt_trichotomy (τ : ℂ).re (1 / 2) with hlt | heq | hgt
    · have hre : 1 / 2 < (reflect (τ : ℂ)).re := by
        simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
      have hrefl : reflect (τ : ℂ) ∈ R := hRall _ (Z.reflect_mem _ τ.2) hre
      have hrr : reflect (reflect (τ : ℂ)) = τ := by simp [reflect]
      have h1 := Wsummand_reflect Z F (Z.reflect_mem _ τ.2)
      rw [hrr] at h1
      have h2 : Z.Wsummand F F (reflect (τ : ℂ)) = (v ⟨reflect τ, hrefl⟩ : ℂ) :=
        hright ⟨reflect τ, hrefl⟩
      have hon0 : onLineSummand Z b τ = 0 := if_neg hlt.ne
      rw [h1, Complex.conj_re, h2, Complex.ofReal_re, hE0 τ hlt.le, hon0]
      linarith [hv0 ⟨reflect τ, hrefl⟩]
    · rw [hE0 τ heq.le, add_zero, onLineSummand, if_pos heq]
      exact re_Wsummand_pairComb_le_of_onLine Z hb hbc (fun ρ => ρ) Δ y heq
    · set ρ₀ : R := ⟨τ, hRall _ τ.2 hgt⟩
      have hEτ : E τ = v ρ₀ := by
        simp only [hEdef]
        rw [Finset.sum_eq_single (f := fun ρ => if τ = ι ρ then v ρ else 0) ρ₀
          (fun ρ _ hρ => if_neg fun (h : τ = ι ρ) => hρ (Subtype.ext (congrArg Subtype.val h).symm))
          (fun h => absurd (Finset.mem_univ _) h), if_pos (Subtype.ext rfl)]
      have hon0 : onLineSummand Z b τ = 0 := if_neg hgt.ne'
      have h2 : Z.Wsummand F F τ = (v ρ₀ : ℂ) := hright ρ₀
      rw [h2, Complex.ofReal_re, hEτ, hon0]
      linarith
  have hEs : ∀ ρ : R, HasSum (fun τ : Z.carrier => if τ = ι ρ then v ρ else 0) (v ρ) :=
    fun ρ => hasSum_ite_eq (ι ρ) (v ρ)
  have hEsum : HasSum E (∑ ρ, v ρ) := hasSum_sum fun ρ _ => hEs ρ
  have hYv : ∑ ρ, v ρ ≤ Y * (-4 * A - 1) := by
    rw [hYdef, Finset.sum_mul]
    exact Finset.sum_le_sum fun ρ _ => hv ρ
  rw [ZeroConfig.W, Complex.re_tsum (summable_Wsummand Z hZ hFd hFc hFd hFc)]
  calc ∑' τ : Z.carrier, (Z.Wsummand F F τ).re ≤ ∑' τ, (4 * Y * onLineSummand Z b τ + E τ) :=
        Summable.tsum_le_tsum hpt (summable_re_Wsummand Z hZ hFd hFc hFd hFc)
          ((hS.mul_left _).add hEsum.summable)
    _ = 4 * Y * A + ∑ ρ, v ρ := by
        rw [Summable.tsum_add (hS.mul_left _) hEsum.summable, tsum_mul_left, hEsum.tsum_eq,
          hAdef, onLineMass]
    _ ≤ 4 * Y * A + Y * (-4 * A - 1) := by linarith
    _ = -Y := by ring

/-- Support of a phased translate `ω b(· − Δ)`. -/
theorem tsupport_phasedTranslate_subset {b : ℝ → ℂ} {a₀ Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hb : tsupport b ⊆ Icc (-a₀) a₀) (ω : ℂ) :
    tsupport (phasedTranslate b ω Δ) ⊆ Icc (-(Δ + a₀)) (Δ + a₀) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hout
  apply hu
  have hu' : u - Δ ∉ Icc (-a₀) a₀ := fun h => hout ⟨by linarith [h.1], by linarith [h.2]⟩
  simp [phasedTranslate, image_eq_zero_of_notMem_tsupport (fun h => hu' (hb h))]

/-- If every `b_ρ` is supported in `[−a₀, a₀]` and `Δ ≥ 0`, every test in `pairFamily b ω Δ` is
supported in `[−(Δ + a₀), Δ + a₀]`. -/
theorem tsupport_pairFamily_subset {R : Type*} {b : R → ℝ → ℂ} {a₀ Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hb : ∀ ρ, tsupport (b ρ) ⊆ Icc (-a₀) a₀) (ω : R → ℂ) (p : R × Fin 2) :
    tsupport (pairFamily b ω Δ p) ⊆ Icc (-(Δ + a₀)) (Δ + a₀) := by
  unfold pairFamily
  split_ifs
  · exact (hb p.1).trans (Set.Icc_subset_Icc (by linarith) (by linarith))
  · exact tsupport_phasedTranslate_subset hΔ (hb p.1) (ω p.1)

/-- Support of `bumpTest δ hδ t` lies in `[t − δ, t + δ]`. -/
theorem tsupport_bumpTest_subset_Icc {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    tsupport (bumpTest δ hδ t) ⊆ Icc (t - δ) (t + δ) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hout
  apply hu
  have hdist : δ ≤ dist (u - t) 0 := by
    rw [Real.dist_0_eq_abs]
    by_contra hlt
    push Not at hlt
    obtain ⟨h1, h2⟩ := abs_lt.mp hlt
    exact hout ⟨by linarith, by linarith⟩
  simp [bumpTest, (smallBump δ hδ).zero_of_le_dist hdist]

/-- **Interpolation of transforms at any prescribed support radius `a₀ > 0`.** -/
theorem exists_test_interpolating_Icc {m : ℕ} {a₀ : ℝ} (ha₀ : 0 < a₀) (z : Fin m → ℂ)
    (hz : Function.Injective z) (val : Fin m → ℂ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a₀) a₀ ∧ ∀ k, paperFT f (z k) = val k := by
  set δ : ℝ := min (a₀ / 2) (1 / (4 * (1 + ∑ k, ‖z k‖)))
  have hS : 0 ≤ ∑ k, ‖z k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδa : δ ≤ a₀ / 2 := min_le_left _ _
  have hzδ : ∀ k, ‖z k‖ * δ ≤ 1 / 4 := by
    intro k
    have hk : ‖z k‖ ≤ ∑ k, ‖z k‖ :=
      Finset.single_le_sum (fun k _ => norm_nonneg (z k)) (Finset.mem_univ k)
    have hδ2 : δ ≤ 1 / (4 * (1 + ∑ k, ‖z k‖)) := min_le_right _ _
    calc ‖z k‖ * δ ≤ ‖z k‖ * (1 / (4 * (1 + ∑ k, ‖z k‖))) :=
          mul_le_mul_of_nonneg_left hδ2 (norm_nonneg _)
      _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  set h : Fin m → ℂ := fun k => paperFT (bumpTest δ hδ 0) (z k)
  have hh : ∀ k, h k ≠ 0 := fun k => paperFT_bumpTest_zero_ne_zero hδ (hzδ k)
  set D : ℝ := 1 + ∑ k, ∑ l, ‖z k - z l‖
  have hD0 : 0 ≤ ∑ k, ∑ l, ‖z k - z l‖ :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _
  set τ : ℝ := min (a₀ / (2 * ((m : ℝ) + 1))) (1 / D)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτa : τ ≤ a₀ / (2 * ((m : ℝ) + 1)) := min_le_left _ _
  have hτD : τ ≤ 1 / D := min_le_right _ _
  set w : Fin m → ℂ := fun k => cexp (I * z k * τ)
  have hw : Function.Injective w := by
    intro k l hkl
    obtain ⟨p, hp⟩ := Complex.exp_eq_exp_iff_exists_int.mp hkl
    have hkl' : (z k - z l) * τ = 2 * Real.pi * p := by
      have := congrArg (fun x => x / I) hp
      field_simp at this
      linear_combination this
    have hle : ‖z k - z l‖ ≤ ∑ k, ∑ l, ‖z k - z l‖ :=
      (Finset.single_le_sum (f := fun l => ‖z k - z l‖) (fun l _ => norm_nonneg _)
        (Finset.mem_univ l)).trans (Finset.single_le_sum (f := fun k => ∑ l, ‖z k - z l‖)
          (fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _) (Finset.mem_univ k))
    have hsmall : ‖(z k - z l) * τ‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
      calc ‖z k - z l‖ * τ ≤ ‖z k - z l‖ * (1 / D) :=
            mul_le_mul_of_nonneg_left hτD (norm_nonneg _)
        _ < 1 := by
            simp only [D]
            rw [mul_one_div, div_lt_one (by positivity)]
            linarith
    have hp0 : p = 0 := by
      by_contra hp0
      rw [hkl', norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity), Complex.norm_intCast] at hsmall
      have h1 : (1 : ℝ) ≤ |(p : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hp0
      have : (2 : ℝ) * Real.pi * 1 ≤ 2 * Real.pi * |(p : ℝ)| := by gcongr
      have := Real.pi_gt_three
      norm_num at hsmall
      nlinarith
    rw [hp0] at hkl'
    simp only [Int.cast_zero, mul_zero] at hkl'
    rcases mul_eq_zero.mp hkl' with h0 | h0
    · exact hz (sub_eq_zero.mp h0)
    · exact absurd h0 (Complex.ofReal_ne_zero.mpr hτ.ne')
  set M : Matrix (Fin m) (Fin m) ℂ := diagonal h * vandermonde w
  have hdet : IsUnit M.det := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
    refine Ne.isUnit (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hh k) ?_)
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero.mpr fun he => by
      have := hw he
      simp only [Finset.mem_Ioi] at hj
      exact (ne_of_gt hj) this
  set c : Fin m → ℂ := M⁻¹ *ᵥ val
  refine ⟨∑ j, c j • bumpTest δ hδ ((j : ℕ) * τ),
    contDiff_sum_smul _ (fun j => bumpTest_contDiff hδ _) c, ?_, fun k => ?_⟩
  · refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra hout
    apply hu
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : ((j : ℕ) : ℝ) ≤ m := by exact_mod_cast j.is_lt.le
    have hjτ : ((j : ℕ) : ℝ) * τ ≤ a₀ / 2 := by
      calc ((j : ℕ) : ℝ) * τ ≤ m * (a₀ / (2 * ((m : ℝ) + 1))) :=
            mul_le_mul hj hτa hτ.le (Nat.cast_nonneg _)
        _ ≤ (m + 1) * (a₀ / (2 * ((m : ℝ) + 1))) := by gcongr; linarith
        _ = a₀ / 2 := by field_simp
    have hj0 : 0 ≤ ((j : ℕ) : ℝ) * τ := by positivity
    have hsub : Icc (((j : ℕ) : ℝ) * τ - δ) (((j : ℕ) : ℝ) * τ + δ) ⊆ Icc (-a₀) a₀ :=
      Set.Icc_subset_Icc (by linarith) (by linarith)
    have : bumpTest δ hδ ((j : ℕ) * τ) u = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hout (hsub (tsupport_bumpTest_subset_Icc hδ _ h))
    simp [this]
  · rw [paperFT_sum_smul _ (fun j => (bumpTest_contDiff hδ _).continuous)
      (fun j => bumpTest_hasCompactSupport hδ _)]
    have hMc : M *ᵥ c = val := by
      simp only [c, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hentry : ∀ j, c j * paperFT (bumpTest δ hδ ((j : ℕ) * τ)) (z k) = M k j * c j := by
      intro j
      rw [paperFT_bumpTest]
      simp only [M, Matrix.mul_apply, Matrix.diagonal_apply, vandermonde_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, w, h, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    rw [Finset.sum_congr rfl fun j _ => hentry j]
    have := congrFun hMc k
    rwa [Matrix.mulVec, dotProduct] at this

/-- **Dual tests supported in `[−a₀, a₀]`.** For any finite set `R` of zeros right of the line and
any `a₀ > 0`, there exist `C²` dual tests `b_ρ` supported in `[−a₀, a₀]`. -/
theorem exists_dual_tests_Icc {R : Finset ℂ} (hR : ∀ ρ ∈ R, 1 / 2 < ρ.re) {a₀ : ℝ}
    (ha₀ : 0 < a₀) :
    ∃ b : R → ℝ → ℂ, (∀ ρ, ContDiff ℝ 2 (b ρ)) ∧ (∀ ρ, tsupport (b ρ) ⊆ Icc (-a₀) a₀) ∧
      (∀ ρ σ : R, paperFT (b ρ) (gammaOf σ) = if σ = ρ then 1 else 0) ∧
      (∀ ρ σ : R, paperFT (b ρ) (conj (gammaOf σ)) = if σ = ρ then 1 else 0) := by
  classical
  set z : R ⊕ R → ℂ := Sum.elim (fun σ => gammaOf σ) (fun σ => conj (gammaOf σ))
  have him : ∀ ρ : ℂ, (gammaOf ρ).im = 1 / 2 - ρ.re := fun ρ => by simp [gammaOf]
  have hz : Function.Injective z := by
    rintro (σ | σ) (σ' | σ') h <;> simp only [z, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (Subtype.ext (gammaOf_injective h))
    · have := congrArg Complex.im h
      rw [Complex.conj_im, him, him] at this
      linarith [hR _ σ.2, hR _ σ'.2]
    · have := congrArg Complex.im h
      rw [Complex.conj_im, him, him] at this
      linarith [hR _ σ.2, hR _ σ'.2]
    · have := congrArg conj h
      simp only [conj_conj] at this
      exact congrArg Sum.inr (Subtype.ext (gammaOf_injective this))
  set e := Fintype.equivFin (R ⊕ R)
  have hze : Function.Injective (z ∘ e.symm) := hz.comp e.symm.injective
  choose b hb hbs hbv using fun ρ : R => exists_test_interpolating_Icc ha₀ (z ∘ e.symm) hze
    ((Sum.elim (fun σ => if σ = ρ then 1 else 0) (fun σ => if σ = ρ then 1 else 0)) ∘ e.symm)
  refine ⟨b, hb, hbs, fun ρ σ => ?_, fun ρ σ => ?_⟩
  · have := hbv ρ (e (Sum.inl σ))
    simpa [Function.comp_apply, z] using this
  · have := hbv ρ (e (Sum.inr σ))
    simpa [Function.comp_apply, z] using this

/-- **Visibility degree from on-line mass.** If `b` is a dual family for the right-zero set `R` of
a tempered configuration `Z`, supported in `[−a₀, a₀]`, and `Δ ≥ 0` satisfies
`2 · onLineMass Z b + ½ ≤ cosh((Re ρ − ½)Δ) − 1` for every `ρ ∈ R`, then at every degree
`a ≥ Δ + a₀` all `|R|` right zeros are visible: `hodgeDefectAt Z a = |R|`. -/
theorem hodgeDefectAt_eq_of_onLineMass (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hR : (rightZeros Z).Finite) {b : hR.toFinset → ℝ → ℂ}
    (hb : ∀ ρ, ContDiff ℝ 2 (b ρ)) {a₀ : ℝ}
    (hbs : ∀ ρ, tsupport (b ρ) ⊆ Icc (-a₀) a₀)
    (hb1 : ∀ ρ σ : hR.toFinset, paperFT (b ρ) (gammaOf σ) = if σ = ρ then 1 else 0)
    (hb2 : ∀ ρ σ : hR.toFinset, paperFT (b ρ) (conj (gammaOf σ)) = if σ = ρ then 1 else 0)
    {Δ a : ℝ} (hΔ0 : 0 ≤ Δ) (ha : Δ + a₀ ≤ a)
    (hΔ : ∀ ρ : hR.toFinset,
      2 * onLineMass Z b + 1 / 2 ≤ Real.cosh (((ρ : ℂ).re - 1 / 2) * Δ) - 1) :
    hodgeDefectAt Z a = hR.toFinset.card := by
  classical
  have hbc : ∀ ρ : hR.toFinset, HasCompactSupport (b ρ) := fun ρ =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hbs ρ)
  have hRm : ∀ ρ : hR.toFinset, (ρ : ℂ) ∈ Z.carrier ∧ 1 / 2 < (ρ : ℂ).re := fun ρ => by
    have := (Set.Finite.mem_toFinset hR).mp ρ.2
    simpa [rightZeros] using this
  have hRall : ∀ τ ∈ Z.carrier, 1 / 2 < τ.re → τ ∈ hR.toFinset := fun τ hτ hre =>
    (Set.Finite.mem_toFinset hR).mpr ⟨hτ, hre⟩
  set F := pairFamily b (fun ρ => phase Δ ρ) Δ
  set e := Fintype.equivFin (hR.toFinset × Fin 2)
  set Ψ : (hR.toFinset → ℂ) →ₗ[ℂ] (Fin (Fintype.card (hR.toFinset × Fin 2)) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (Prod.fst ∘ e.symm)
  have hΨ : Function.Injective Ψ :=
    LinearMap.funLeft_injective_of_surjective ℂ ℂ (Prod.fst ∘ e.symm) fun ρ =>
      ⟨e (ρ, 0), by simp⟩
  have hFc : ∀ j, ContDiff ℝ 2 (F j) := pairFamily_contDiff hb (fun ρ => phase Δ ρ) Δ
  have hFcs : ∀ j, HasCompactSupport (F j) :=
    pairFamily_hasCompactSupport hbc (fun ρ => phase Δ ρ) Δ
  have hpd : IsPosDefOn (-(zeroGram Z (F ∘ e.symm))) (LinearMap.range Ψ) := by
    intro x hx hx0
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    have hy : y ≠ 0 := fun h => hx0 (by rw [h, map_zero])
    obtain ⟨ρ, hρ⟩ := Function.ne_iff.mp hy
    have hYpos : 0 < ∑ σ, ‖y σ‖ ^ 2 :=
      lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun σ => ‖y σ‖ ^ 2)
        (fun σ _ => by positivity) (Finset.mem_univ ρ))
    rw [hermQuad_neg, hermQuad_zeroGram_of_tempered Z hZ (F ∘ e.symm)
      (fun i => hFc (e.symm i)) (fun i => hFcs (e.symm i))]
    have hsum : (∑ i, conj (Ψ y i) • (F ∘ e.symm) i) =
        ∑ p : hR.toFinset × Fin 2, conj (y p.1) • F p := by
      simp only [Ψ, LinearMap.funLeft_apply, Function.comp_apply]
      exact e.symm.sum_comp fun p => conj (y p.1) • F p
    rw [hsum]
    linarith [re_W_pairComb_le_of_onLineMass Z hZ hRm hRall hb hbc hb1 hb2 hΔ y]
  have hneg : hR.toFinset.card ≤ hermNegIndex (zeroGram Z (F ∘ e.symm)) := by
    have h1 := finrank_le_posIndex hpd
    rw [LinearMap.finrank_range_of_inj hΨ, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe] at h1
    rw [hermNegIndex]
    exact h1
  have hFs : ∀ j, tsupport (F j) ⊆ Icc (-(Δ + a₀)) (Δ + a₀) :=
    tsupport_pairFamily_subset hΔ0 hbs (fun ρ => phase Δ ρ)
  have hge : (hR.toFinset.card : ℕ∞) ≤ hodgeDefectAt Z a := by
    refine (ENat.coe_le_coe.mpr hneg).trans
      (le_hodgeDefectAt Z (F ∘ e.symm) fun i => ⟨hFc (e.symm i), ?_⟩)
    exact (hFs (e.symm i)).trans (Set.Icc_subset_Icc (by linarith) (by linarith))
  have hle : hodgeDefectAt Z a ≤ hR.toFinset.card := by
    rw [← hR.encard_eq_coe_toFinset_card]
    exact hodgeDefectAt_le Z hZ a
  exact le_antisymm hle hge

/-- **Logarithmic visibility degree from on-line mass.** Since `cosh x ≥ e^x / 2`, all `|R|` right
zeros are visible at every degree `a ≥ a₀ + Δ` once
`log(4 · onLineMass Z b + 3) ≤ (Re ρ − ½) Δ` for every `ρ ∈ R`. -/
theorem hodgeDefectAt_eq_of_log_onLineMass (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hR : (rightZeros Z).Finite) {b : hR.toFinset → ℝ → ℂ}
    (hb : ∀ ρ, ContDiff ℝ 2 (b ρ)) {a₀ : ℝ}
    (hbs : ∀ ρ, tsupport (b ρ) ⊆ Icc (-a₀) a₀)
    (hb1 : ∀ ρ σ : hR.toFinset, paperFT (b ρ) (gammaOf σ) = if σ = ρ then 1 else 0)
    (hb2 : ∀ ρ σ : hR.toFinset, paperFT (b ρ) (conj (gammaOf σ)) = if σ = ρ then 1 else 0)
    {Δ a : ℝ} (hΔ0 : 0 ≤ Δ) (ha : Δ + a₀ ≤ a)
    (hlog : ∀ ρ : hR.toFinset,
      Real.log (4 * onLineMass Z b + 3) ≤ ((ρ : ℂ).re - 1 / 2) * Δ) :
    hodgeDefectAt Z a = hR.toFinset.card := by
  refine hodgeDefectAt_eq_of_onLineMass Z hZ hR hb hbs hb1 hb2 hΔ0 ha fun ρ => ?_
  have hA0 := onLineMass_nonneg Z b
  have hexp : 4 * onLineMass Z b + 3 ≤ Real.exp (((ρ : ℂ).re - 1 / 2) * Δ) := by
    rw [← Real.exp_log (by linarith : 0 < 4 * onLineMass Z b + 3)]
    exact Real.exp_le_exp.mpr (hlog ρ)
  have hpos := (Real.exp_pos (-(((ρ : ℂ).re - 1 / 2) * Δ))).le
  rw [Real.cosh_eq]
  linarith

/-- **Exact on-line mass identity for `multiPairConfig`.** Below the Nyquist degree `L/2`, Poisson
summation evaluates the on-line zero mass of any family `b` on `multiPairConfig` in closed form:
`onLineMass = 2L Σ_ρ ∫ ‖b_ρ‖²`. -/
theorem onLineMass_multiPairConfig_eq {L : ℝ} (hL : 0 < L) {n : ℕ} (δ γ : Fin n → ℝ)
    (hδ : ∀ k, 0 < δ k) (hδ' : ∀ k, δ k ≤ 1 / 2)
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k))
    {R : Type*} [Fintype R] {b : R → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ))
    (hbs : ∀ ρ, tsupport (b ρ) ⊆ Icc (-(L / 2)) (L / 2)) :
    onLineMass (multiPairConfig hL δ γ hδ hδ') b =
      2 * L * ∑ ρ : R, ∫ t, ‖b ρ t‖ ^ 2 := by
  set Z := multiPairConfig hL δ γ hδ hδ'
  have hmultdef : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else 1 := fun _ => rfl
  have hmult : ∀ m : ℤ, Z.mult (RHTower.verticalLatticePoint L 0 m) = 2 := fun m => by
    rw [hmultdef, if_pos (by simp [RHTower.verticalLatticePoint])]
  set G : ℂ → ℝ := fun τ =>
    if τ.re = 1 / 2 then ∑ ρ : R, (Z.mult τ : ℝ) * ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2 else 0
  have hon_each : ∀ ρ : R, HasSum (fun τ : Set.range (RHTower.verticalLatticePoint L 0) =>
      (Z.mult τ : ℝ) * ‖paperFT (b ρ) (gammaOf τ)‖ ^ 2) (2 * L * ∫ t, ‖b ρ t‖ ^ 2) := by
    intro ρ
    have hW := Complex.hasSum_re (hasSum_Wsummand_onLineLattice Z hL hmult (hb ρ)
      (hb ρ).continuous (hbs ρ) (hbs ρ))
    rw [integral_mul_conj_self_eq, show (2 * (L : ℂ) * ((∫ t, ‖b ρ t‖ ^ 2 : ℝ) : ℂ)).re =
      2 * L * ∫ t, ‖b ρ t‖ ^ 2 by
      rw [show (2 * (L : ℂ) * ((∫ t, ‖b ρ t‖ ^ 2 : ℝ) : ℂ)) =
        ((2 * L * ∫ t, ‖b ρ t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]] at hW
    refine hW.congr_fun fun τ => ?_
    obtain ⟨_, m, rfl⟩ := τ
    have hre : (RHTower.verticalLatticePoint L 0 m).re = 1 / 2 := by
      simp [RHTower.verticalLatticePoint]
    have hγ : conj (gammaOf (RHTower.verticalLatticePoint L 0 m)) =
        gammaOf (RHTower.verticalLatticePoint L 0 m) := by
      rw [Complex.conj_eq_iff_im]; simp [gammaOf, hre]
    rw [ZeroConfig.Wsummand, hγ, mul_assoc, Complex.mul_conj, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have h₁ : HasSum (fun τ : Set.range (RHTower.verticalLatticePoint L 0) => G τ)
      (2 * L * ∑ ρ : R, ∫ t, ‖b ρ t‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine (hasSum_sum fun ρ _ => hon_each ρ).congr_fun fun τ => ?_
    obtain ⟨_, m, rfl⟩ := τ
    have hre : (RHTower.verticalLatticePoint L 0 m).re = 1 / 2 := by
      simp [RHTower.verticalLatticePoint]
    simp [G, hre]
  have hp : HasSum (fun τ : Set.range (fun k : Fin n => offLinePoint (δ k) (γ k)) => G τ) 0 := by
    rw [hinj.hasSum_range_iff]
    have h0 : ∀ k : Fin n, G (offLinePoint (δ k) (γ k)) = 0 := fun k =>
      if_neg (by simp only [offLinePoint]; linarith [hδ k])
    simp [Function.comp_def, h0]
  have hinj' := injective_offLinePoint_neg_of_pos δ γ hinj
  have hq : HasSum (fun τ : Set.range (fun k : Fin n => offLinePoint (-δ k) (γ k)) => G τ) 0 := by
    rw [hinj'.hasSum_range_iff]
    have h0 : ∀ k : Fin n, G (offLinePoint (-δ k) (γ k)) = 0 := fun k =>
      if_neg (by simp only [offLinePoint]; linarith [hδ k])
    simp [Function.comp_def, h0]
  have hall := HasSum.add_disjoint (f := G) (disjoint_onLine_pos_offLine_neg δ γ hδ L)
    (HasSum.add_disjoint (f := G) (disjoint_onLine_offLine_pos δ γ hδ L) h₁ hp) hq
  rw [onLineMass]
  exact hall.tsum_eq.trans (by ring)

/-- **Explicit visibility degree of `n` pairs in `multiPairConfig`.** With dual tests `b` supported
in `[−a₀, a₀]` (`a₀ ≤ L/2`), all `n` right zeros of `multiPairConfig` are visible at every
degree `a ≥ a₀ + Δ` once `4L Σ_ρ ∫ ‖b_ρ‖² + ½ ≤ cosh((Re ρ − ½)Δ) − 1`. -/
theorem hodgeDefectAt_multiPairConfig_eq_card {L : ℝ} (hL : 0 < L) {n : ℕ} (δ γ : Fin n → ℝ)
    (hδ : ∀ k, 0 < δ k) (hδ' : ∀ k, δ k ≤ 1 / 2)
    (hinj : Function.Injective fun k : Fin n => offLinePoint (δ k) (γ k))
    (hR : (rightZeros (multiPairConfig hL δ γ hδ hδ')).Finite)
    {b : hR.toFinset → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ)) {a₀ : ℝ}
    (ha₀L : a₀ ≤ L / 2) (hbs : ∀ ρ, tsupport (b ρ) ⊆ Icc (-a₀) a₀)
    (hb1 : ∀ ρ σ : hR.toFinset, paperFT (b ρ) (gammaOf σ) = if σ = ρ then 1 else 0)
    (hb2 : ∀ ρ σ : hR.toFinset, paperFT (b ρ) (conj (gammaOf σ)) = if σ = ρ then 1 else 0)
    {Δ a : ℝ} (hΔ0 : 0 ≤ Δ) (ha : Δ + a₀ ≤ a)
    (hΔ : ∀ ρ : hR.toFinset,
      4 * L * (∑ σ : hR.toFinset, ∫ t, ‖b σ t‖ ^ 2) + 1 / 2 ≤
        Real.cosh (((ρ : ℂ).re - 1 / 2) * Δ) - 1) :
    hodgeDefectAt (multiPairConfig hL δ γ hδ hδ') a = n := by
  have hcard : (hR.toFinset.card : ℕ∞) = n := by
    rw [← hR.encard_eq_coe_toFinset_card, encard_rightZeros_multiPairConfig hL δ γ hδ hδ' hinj]
  rw [← hcard]
  refine hodgeDefectAt_eq_of_onLineMass _ (temperedConfig_multiPairConfig hL δ γ hδ hδ') hR
    hb hbs hb1 hb2 hΔ0 ha fun ρ => ?_
  have hbs' : ∀ σ, tsupport (b σ) ⊆ Icc (-(L / 2)) (L / 2) := fun σ =>
    (hbs σ).trans (Set.Icc_subset_Icc (by linarith) ha₀L)
  rw [onLineMass_multiPairConfig_eq hL δ γ hδ hδ' hinj hb hbs']
  linarith [hΔ ρ]

/-- **Explicit on-line mass bound under local density `M`.** If a configuration `Z` has at most `M`
on-line zeros (each of multiplicity `≤ m₀`) in every unit-radius height window `[T − 1, T + 1]`,
then for any test family `b` supported in `[−a₀, a₀]` (`a₀ > 0`),
`onLineMass Z b ≤ m₀ M (2a₀ + 2π) e^{2π} Σ_ρ ∫ ‖b_ρ‖²`. -/
theorem onLineMass_le_of_locallyBounded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {m₀ M : ℕ} (hm₀ : ∀ τ ∈ Z.carrier, τ.re = 1 / 2 → Z.mult τ ≤ m₀)
    (hM : ∀ T : ℝ,
      ({τ : Z.carrier | (τ : ℂ).re = 1 / 2 ∧ |(τ : ℂ).im - T| ≤ 1} : Set Z.carrier).encard ≤ M)
    {R : Type*} [Fintype R] {b : R → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ))
    {a₀ : ℝ} (ha₀ : 0 < a₀) (hbs : ∀ ρ, tsupport (b ρ) ⊆ Icc (-a₀) a₀) :
    onLineMass Z b ≤
      m₀ * M * ((2 * a₀ + 2 * π) * Real.exp (2 * π)) * ∑ ρ : R, ∫ u, ‖b ρ u‖ ^ 2 := by
  classical
  have hbc : ∀ ρ, HasCompactSupport (b ρ) := fun ρ =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hbs ρ)
  have hsrc : ∀ ρ, RHTower.CCMParityQuartet.IntervalSource a₀ (b ρ) := fun ρ =>
    { continuous := (hb ρ).continuous
      hasCompactSupport := hbc ρ
      vanish := fun u hu => image_eq_zero_of_notMem_tsupport fun h => hu (hbs ρ h) }
  set Q := {τ : Z.carrier // (τ : ℂ).re = 1 / 2}
  set x : Q → ℝ := fun q => ((q : Z.carrier) : ℂ).im
  set y : Q → ℝ := fun _ => 0
  have hMQ : ∀ T : ℝ, ({q : Q | |x q - T| ≤ 1} : Set Q).encard ≤ M := by
    intro T
    have hinj : Function.Injective (Subtype.val : Q → Z.carrier) := Subtype.val_injective
    rw [← hinj.encard_image]
    refine (Set.encard_le_encard ?_).trans (hM T)
    rintro τ ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩
  have hγq : ∀ q : Q, gammaOf ((q : Z.carrier) : ℂ) = (x q : ℂ) + (y q : ℂ) * I := by
    intro q
    apply Complex.ext
    · simp [gammaOf, x, y]
    · simp [gammaOf, x, y, q.2]
  have hρ_bound : ∀ ρ : R,
      Summable (fun q : Q => ‖paperFT (b ρ) (gammaOf ((q : Z.carrier) : ℂ))‖ ^ 2) ∧
        (∑' q : Q, ‖paperFT (b ρ) (gammaOf ((q : Z.carrier) : ℂ))‖ ^ 2) ≤
          M * ((2 * a₀ + 2 * π) * Real.exp (2 * π)) * ∫ u, ‖b ρ u‖ ^ 2 := by
    intro ρ
    obtain ⟨hs, hle⟩ := summable_tsum_norm_sq_testTransform_le_of_locallyBounded (σ := 0) ha₀
      (hsrc ρ) x y (le_refl (0 : ℝ)) (fun _ => by simp [y]) hMQ
    rw [mul_zero, zero_mul, Real.exp_zero, mul_one] at hle
    have hfun : (fun q : Q => ‖paperFT (b ρ) (gammaOf ((q : Z.carrier) : ℂ))‖ ^ 2) =
        fun q : Q => ‖testTransform (b ρ) ((x q : ℂ) + (y q : ℂ) * I)‖ ^ 2 := by
      funext q
      rw [hγq q]
      rfl
    rw [hfun]
    exact ⟨hs, hle⟩
  have hS : Summable (onLineSummand Z b) := summable_onLineSummand Z hZ hb hbc
  have hsupp : Function.support (onLineSummand Z b) ⊆ {τ : Z.carrier | (τ : ℂ).re = 1 / 2} := by
    intro τ hτ
    by_contra hne
    exact hτ (if_neg hne)
  rw [onLineMass, ← tsum_subtype_eq_of_support_subset hsupp]
  have hpt : ∀ q : Q, onLineSummand Z b q ≤
      ∑ ρ : R, (m₀ : ℝ) * ‖paperFT (b ρ) (gammaOf ((q : Z.carrier) : ℂ))‖ ^ 2 := by
    intro q
    rw [onLineSummand, if_pos q.2]
    refine Finset.sum_le_sum fun ρ _ => ?_
    have hm : (Z.mult ((q : Z.carrier) : ℂ) : ℝ) ≤ m₀ := by
      exact_mod_cast hm₀ q.1 q.1.2 q.2
    exact mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  have hsum_rhs : Summable fun q : Q =>
      ∑ ρ : R, (m₀ : ℝ) * ‖paperFT (b ρ) (gammaOf ((q : Z.carrier) : ℂ))‖ ^ 2 :=
    summable_sum fun ρ _ => (hρ_bound ρ).1.mul_left _
  calc (∑' q : Q, onLineSummand Z b q)
      ≤ ∑' q : Q, ∑ ρ : R, (m₀ : ℝ) * ‖paperFT (b ρ) (gammaOf ((q : Z.carrier) : ℂ))‖ ^ 2 :=
        Summable.tsum_le_tsum hpt (hS.subtype _) hsum_rhs
    _ = ∑ ρ : R, (m₀ : ℝ) * ∑' q : Q, ‖paperFT (b ρ) (gammaOf ((q : Z.carrier) : ℂ))‖ ^ 2 := by
        rw [Summable.tsum_finsetSum fun ρ _ => (hρ_bound ρ).1.mul_left _]
        exact Finset.sum_congr rfl fun ρ _ => tsum_mul_left
    _ ≤ ∑ ρ : R, (m₀ : ℝ) * ((M * ((2 * a₀ + 2 * π) * Real.exp (2 * π))) * ∫ u, ‖b ρ u‖ ^ 2) :=
        Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hρ_bound ρ).2 (Nat.cast_nonneg _)
    _ = m₀ * M * ((2 * a₀ + 2 * π) * Real.exp (2 * π)) * ∑ ρ : R, ∫ u, ‖b ρ u‖ ^ 2 := by
        simp only [← Finset.mul_sum]; ring

/-- **Explicit visibility degree of `n` right zeros under local density `M`.** For any tempered
configuration `Z` with finite right-zero set `R`, at most `M` on-line zeros of multiplicity `≤ m₀`
per unit-radius window, and dual tests `b_ρ` supported in `[−a₀, a₀]` (`a₀ > 0`), all `|R|` right
zeros become visible (`hodgeDefectAt Z a = |R|`) at every degree `a ≥ a₀ + Δ` with
`log(4 m₀ M (2a₀ + 2π) e^{2π} Σ_ρ ∫ ‖b_ρ‖² + 3) ≤ (Re ρ − ½) Δ`. -/
theorem hodgeDefectAt_eq_of_locallyBounded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hR : (rightZeros Z).Finite) {m₀ M : ℕ}
    (hm₀ : ∀ τ ∈ Z.carrier, τ.re = 1 / 2 → Z.mult τ ≤ m₀)
    (hM : ∀ T : ℝ,
      ({τ : Z.carrier | (τ : ℂ).re = 1 / 2 ∧ |(τ : ℂ).im - T| ≤ 1} : Set Z.carrier).encard ≤ M)
    {b : hR.toFinset → ℝ → ℂ} (hb : ∀ ρ, ContDiff ℝ 2 (b ρ)) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hbs : ∀ ρ, tsupport (b ρ) ⊆ Icc (-a₀) a₀)
    (hb1 : ∀ ρ σ : hR.toFinset, paperFT (b ρ) (gammaOf σ) = if σ = ρ then 1 else 0)
    (hb2 : ∀ ρ σ : hR.toFinset, paperFT (b ρ) (conj (gammaOf σ)) = if σ = ρ then 1 else 0)
    {Δ a : ℝ} (hΔ0 : 0 ≤ Δ) (ha : Δ + a₀ ≤ a)
    (hlog : ∀ ρ : hR.toFinset,
      Real.log (4 * (m₀ * M * ((2 * a₀ + 2 * π) * Real.exp (2 * π)) *
        ∑ σ : hR.toFinset, ∫ u, ‖b σ u‖ ^ 2) + 3) ≤ ((ρ : ℂ).re - 1 / 2) * Δ) :
    hodgeDefectAt Z a = hR.toFinset.card := by
  refine hodgeDefectAt_eq_of_log_onLineMass Z hZ hR hb hbs hb1 hb2 hΔ0 ha fun ρ => ?_
  have hle := onLineMass_le_of_locallyBounded Z hZ hm₀ hM hb ha₀ hbs
  have hA0 := onLineMass_nonneg Z b
  refine (Real.log_le_log (by linarith) (by linarith)).trans (hlog ρ)

/-! ### 4. Separated right zeros under logarithmic local density and the scaling surface of `ℤ` -/

/-- **Visibility degree of `n` separated right zeros under logarithmic local count.** Let `Z` be a
tempered configuration with local zero count `N(t, t+1] ≤ A₀ log(|t| + 3)`, and let `T` be a finite
set of right zeros of depth `≥ δ > 0` and height `≤ H_m`, pairwise `2R` apart (`R ≥ 1`) and
isolated at radius `R` from other off-line zeros. Whenever `0 < visibleMargin A₀ a δ R Hm`, the
modulated sinh-tests at the heights of `T` span a `|T|`-dimensional negative subspace of
`zeroGram`, so `(|T| : ℕ∞) ≤ hodgeDefectAt Z a` (with no finiteness hypothesis on `rightZeros Z`
and no loss of polar dimensions). -/
theorem card_le_hodgeDefectAt_of_visible_pairs (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {A₀ : ℝ} (hA₀ : 1 ≤ A₀) (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {a δ R Hm : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hR : 1 ≤ R) (T : Finset ℂ)
    (hT : ∀ ρ ∈ T, ρ ∈ Z.carrier ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ Hm)
    (hsep : ∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|)
    (hiso : ∀ ρ ∈ T, ∀ σ ∈ Z.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R → σ.re = 1 / 2)
    (hvis : 0 < RHTower.visibleMargin A₀ a δ R Hm) :
    (T.card : ℕ∞) ≤ hodgeDefectAt Z a ∧
      ∃ f : Fin T.card → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧
        (∀ i, tsupport (f i) ⊆ Icc (-a) a) ∧ T.card ≤ hermNegIndex (zeroGram Z f) := by
  classical
  set e := T.equivFin
  set s := RHTower.sinhTest a δ
  set f : Fin T.card → ℝ → ℂ := fun i => RHTower.modulatedTest (e.symm i : ℂ).im s
  have hs : ContDiff ℝ 2 s := RHTower.sinhTest_contDiff a δ
  have hsupp : ∀ u, s u ≠ 0 → |u| ≤ a := RHTower.sinhTest_supp ha
  have hfd : ∀ i, ContDiff ℝ 2 (f i) := fun i => RHTower.modulatedTest_contDiff _ hs
  have hfs : ∀ i, tsupport (f i) ⊆ Icc (-a) a := fun i =>
    RHTower.tsupport_modulatedTest_subset _ hsupp
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hfs i)
  have hvis' : 384 * A₀ * Real.log (Hm + 3) * RHTower.testNorm s ^ 2 *
      (1 + Real.exp a / (1 + R)) + 64 * Real.exp a * RHTower.testNorm s ^ 2 *
        (2 * (A₀ * (10 * Real.log (Hm + 3) + 48))) * (10 / R ^ 2) <
      2 * (∫ u, s u * Real.sinh (δ * u)) ^ 2 := by
    unfold RHTower.visibleMargin at hvis; linarith
  have hpd : IsPosDefOn (-(zeroGram Z f)) ⊤ := by
    intro x _ hx0
    rw [hermQuad_neg, hermQuad_zeroGram_of_tempered Z hZ f hfd hfc]
    set c : T → ℂ := fun ρ => conj (x (e ρ))
    have hc0 : c ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
      intro h
      apply hi
      have h1 : c (e.symm i) = 0 := congrFun h (e.symm i)
      simp only [c, Equiv.apply_symm_apply, map_eq_zero] at h1
      exact h1
    have hfun : (∑ i, conj (x i) • f i) =
        fun u => ∑ ρ ∈ T, RHTower.extendCoeff T c ρ * RHTower.modulatedTest ρ.im s u := by
      rw [← RHTower.visibleCombination_eq]
      funext u
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RHTower.visibleCombination]
      rw [← Equiv.sum_comp e (fun i => conj (x i) * f i u)]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp [f, c]
    rw [hfun]
    have hneg := RHTower.re_W_visible_combination_neg Z hA₀ hloc ha hδ hR T hT hsep hiso hvis'
      (RHTower.extendCoeff T c) (RHTower.exists_extendCoeff_ne hc0)
    linarith
  have hneg : T.card ≤ hermNegIndex (zeroGram Z f) := by
    have h1 := finrank_le_posIndex hpd
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    rw [hermNegIndex]
    exact h1
  exact ⟨(ENat.coe_le_coe.mpr hneg).trans (le_hodgeDefectAt Z f fun i => ⟨hfd i, hfs i⟩),
    f, hfd, hfs, hneg⟩

/-- **Unconditional degree-`a` visibility law for the scaling surface of `ℤ`.** There is an
explicit local-count constant `A₀ ≥ 1` such that for any finite set `T` of separated isolated right
zeros of `ζ` of depth `≥ δ > 0` and height `≤ H_m` with `0 < visibleMargin A₀ a δ R Hm`, the degree-`a`
Hodge defect of `ζ` is at least `|T|` and the arithmetic intersection form `intersectionGram Λ`
has at least `1 + |T|` positive squares on `C²` cycles supported in `[−a, a]`. -/
theorem zeta_intersectionGram_posIndex_ge_of_visible_pairs :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ (a δ R Hm : ℝ) (T : Finset ℂ), 0 ≤ a → 0 < δ → 1 ≤ R →
        (∀ ρ ∈ T, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ Hm) →
        (∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|) →
        (∀ ρ ∈ T, ∀ σ ∈ zetaZeroConfig.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R →
          σ.re = 1 / 2) →
        0 < RHTower.visibleMargin A₀ a δ R Hm →
        (T.card : ℕ∞) ≤ hodgeDefectAt zetaZeroConfig a ∧
          ∃ f : Fin T.card → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧
            (∀ i, tsupport (f i) ⊆ Icc (-a) a) ∧
            1 + T.card ≤
              hermPosIndex (intersectionGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) f) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, fun a δ R Hm T ha hδ hR hT hsep hiso hvis => ?_⟩
  obtain ⟨hdef, f, hfd, hfs, hneg⟩ := card_le_hodgeDefectAt_of_visible_pairs zetaZeroConfig
    temperedConfig_zetaZeroConfig hA₀ hloc ha hδ hR T hT hsep hiso hvis
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hfs i)
  refine ⟨hdef, f, hfd, hfs, ?_⟩
  rw [posIndex_intersectionGram, weilGram_eq_zeroGram f hfd hfc]
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
