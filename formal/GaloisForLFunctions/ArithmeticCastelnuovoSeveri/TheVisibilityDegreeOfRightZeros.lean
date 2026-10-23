import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfAnIsolatedPair
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
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

/-- Circle reflection bijects the outer spectrum onto the inner spectrum. -/
theorem card_innerSpectrum_eq_card_outerSpectrum :
    D.innerSpectrum.card = D.outerSpectrum.card := by
  refine Finset.card_bij (fun z _ => circleReflect z) (fun z hz => ?_) (fun z₁ _ z₂ _ h => ?_)
    (fun w hw => ?_)
  · obtain ⟨hzs, hz1⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨D.circleReflect_mem_spectrum hzs,
      by rw [norm_circleReflect]; exact inv_lt_one_of_one_lt₀ hz1⟩
  · have := congrArg circleReflect h
    simpa [circleReflect_circleReflect] using this
  · obtain ⟨hws, hw1⟩ := Finset.mem_filter.mp hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hws
    refine ⟨circleReflect (D.β i), Finset.mem_filter.mpr ⟨D.circleReflect_mem_spectrum hws, ?_⟩,
      circleReflect_circleReflect _⟩
    rw [norm_circleReflect]
    exact one_lt_inv₀ (norm_pos_iff.mpr (D.β_ne_zero i)) |>.mpr hw1

/-- The spectrum partitions into the on-circle eigenvalues and the reflected outer/inner pairs:
`|spectrum| = |onCircleSpectrum| + 2 |outerSpectrum|`. -/
theorem card_spectrum_eq_onCircle_add_two_mul_outer :
    D.spectrum.card = D.onCircleSpectrum.card + 2 * D.outerSpectrum.card := by
  have h1 : D.spectrum.card =
      (D.spectrum.filter fun z => ‖z‖ = 1).card + (D.spectrum.filter fun z => ¬‖z‖ = 1).card :=
    (Finset.filter_card_add_filter_neg_card_eq_card _).symm
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
    · exact Or.inl (Or.inl ⟨-k, by
        rw [SquareRootThreshold.reflect_verticalLatticePoint, neg_zero]⟩)
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

theorem disjoint_onLine_offLine_pos :
    Disjoint (Set.range (RHTower.verticalLatticePoint L 0))
      (Set.range fun k : Fin n => offLinePoint (δ k) (γ k)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨m, rfl⟩ ⟨k, hk⟩
  have := congrArg Complex.re hk
  simp only [RHTower.verticalLatticePoint, offLinePoint] at this
  linarith [hδ k]

theorem disjoint_onLine_pos_offLine_neg :
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
  ext <;> simp only [offLinePoint] <;> linarith

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
  exact ⟨_, HasSum.add_disjoint (f := G) (disjoint_onLine_pos_offLine_neg δ γ hδ)
    (HasSum.add_disjoint (f := G) (disjoint_onLine_offLine_pos δ γ hδ) ha' (hasSum_fintype _))
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
  rw [rightZeros_multiPairConfig, Set.encard_range_of_injective hinj, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin]

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
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) (disjoint_onLine_pos_offLine_neg δ γ hδ)
    (HasSum.add_disjoint (f := Z.Wsummand f f) (disjoint_onLine_offLine_pos δ γ hδ) h₁ hp) hq
  rw [ZeroConfig.W, hall.tsum_eq, add_assoc, ← Finset.sum_add_distrib]

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
      -(if k ∈ S then 0 else 2 * pairEnergy (δ k) a * ∫ t, ‖f t‖ ^ 2) ≤
        (‖paperFT f ((γ k : ℂ) - I * δ k) + paperFT f ((γ k : ℂ) + I * δ k)‖ ^ 2 -
          ‖paperFT f ((γ k : ℂ) - I * δ k) - paperFT f ((γ k : ℂ) + I * δ k)‖ ^ 2) / 2 := by
    intro k
    have hpos : 0 ≤ ‖paperFT f ((γ k : ℂ) - I * δ k) + paperFT f ((γ k : ℂ) + I * δ k)‖ ^ 2 :=
      sq_nonneg _
    by_cases hk : k ∈ S
    · rw [if_pos hk, hnode k hk, sub_self, norm_zero]
      linarith
    · rw [if_neg hk]
      have hsub := norm_sub_sq_le_pairEnergy (hδ k) ha (γ k) hf.continuous hfs
      linarith
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm k
  have hcompl : ∑ k : Fin n, -(if k ∈ S then 0 else 2 * pairEnergy (δ k) a * ∫ t, ‖f t‖ ^ 2) =
      -2 * (∑ k ∈ Sᶜ, pairEnergy (δ k) a) * ∫ t, ‖f t‖ ^ 2 := by
    simp only [neg_ite, neg_zero]
    rw [← Finset.sum_filter_not, Finset.filter_not, Finset.univ_sdiff, ← Finset.sum_mul]
    simp [Finset.mul_sum, mul_assoc]
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
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : f i u = 0 := image_eq_zero_of_notMem_tsupport fun h => hout ((hf i).2 h)
    simp [this]
  have hnode : ∀ k ∈ S, paperFT F ((γ k : ℂ) - I * δ k) = paperFT F ((γ k : ℂ) + I * δ k) := by
    intro k hk
    have h0 := hx ⟨k, hk⟩
    simp only [Lmap, LinearMap.sub_apply, evalFunctional_eq f (fun i => (hf i).1.continuous) hfc,
      sub_eq_zero] at h0
    exact congrArg conj h0
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

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
