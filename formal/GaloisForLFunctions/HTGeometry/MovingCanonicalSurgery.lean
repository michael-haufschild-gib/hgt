import GaloisForLFunctions.HTGeometry.PoleLocalizedExactNegativeSquares
import GaloisForLFunctions.HTGeometry.MovingCanonicalFullTranslationFreeness
import GaloisForLFunctions.HTGeometry.CanonicalProductPredicateSplit

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology Filter Matrix
open scoped ComplexConjugate ComplexOrder BigOperators

noncomputable section

theorem complex_posSemidef_of_tendsto
    {α n : Type*} [Fintype n]
    {l : Filter α} [l.NeBot]
    {A : α → Matrix n n ℂ} {M : Matrix n n ℂ}
    (hA : ∀ᶠ a in l, (A a).PosSemidef)
    (hlim : Tendsto A l (nhds M)) :
    M.PosSemidef := by
  have hMherm : M.IsHermitian := by
    rw [Matrix.IsHermitian]
    have hc : Continuous
        (fun N : Matrix n n ℂ => N.conjTranspose) := by
      fun_prop
    have hleft : Tendsto
        (fun a => (A a).conjTranspose) l
        (nhds M.conjTranspose) :=
      hc.continuousAt.tendsto.comp hlim
    have hright : Tendsto
        (fun a => (A a).conjTranspose) l (nhds M) := by
      apply hlim.congr'
      filter_upwards [hA] with a ha
      exact ha.isHermitian.eq.symm
    exact tendsto_nhds_unique hleft hright
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hMherm
  intro x
  let q : Matrix n n ℂ → ℂ :=
    fun N => star x ⬝ᵥ N.mulVec x
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hq : Tendsto (fun a => q (A a)) l (nhds (q M)) :=
    hqcont.continuousAt.tendsto.comp hlim
  have hre : Tendsto (fun a => (q (A a)).re) l
      (nhds (q M).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hq
  have him : Tendsto (fun a => (q (A a)).im) l
      (nhds (q M).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hq
  rw [Complex.nonneg_iff]
  constructor
  · apply isClosed_Ici.mem_of_tendsto hre
    filter_upwards [hA] with a ha
    exact (RCLike.nonneg_iff.mp
      (ha.dotProduct_mulVec_nonneg x)).1
  · have him0 : Tendsto (fun _ : α => (0 : ℝ)) l
        (nhds (0 : ℝ)) := tendsto_const_nhds
    apply tendsto_nhds_unique him0
    apply him.congr'
    filter_upwards [hA] with a ha
    exact (RCLike.nonneg_iff.mp
      (ha.dotProduct_mulVec_nonneg x)).2

theorem tsum_outer_posSemidef
    {ι : Type*} {N : ℕ} (v : ι → Fin N → ℂ)
    (hsum : ∀ j l, Summable (fun i => v i j * star (v i l))) :
    (Matrix.of (fun j l => ∑' i, v i j * star (v i l))).PosSemidef := by
  let A : Finset ι → Matrix (Fin N) (Fin N) ℂ :=
    fun s => ∑ i ∈ s,
      Matrix.of (fun j l => v i j * star (v i l))
  apply complex_posSemidef_of_tendsto
    (α := Finset ι) (n := Fin N)
    (l := (SummationFilter.unconditional ι).filter)
    (A := A)
    (M := Matrix.of (fun j l =>
      ∑' i, v i j * star (v i l)))
  · exact Filter.Eventually.of_forall fun s =>
      Matrix.posSemidef_sum s
        (fun i _ => GaloisForLFunctions.outer_posSemidef (v i))
  · change Tendsto
      (fun s j l => A s j l)
      (SummationFilter.unconditional ι).filter
      (nhds (fun j l => ∑' i, v i j * star (v i l)))
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_pi_nhds]
    intro l
    simpa only [A, Matrix.sum_apply, Matrix.of_apply, HasSum] using
      (hsum j l).hasSum

def movingCanonicalRegularizedAtom
    (θ : BoundedRealSequence) (n : ℕ) (z : ℂ) : ℂ :=
  ((movingCanonicalZero θ n : ℂ) - z)⁻¹ -
    (movingCanonicalZero θ n : ℂ)⁻¹

def movingCanonicalComplementCarrier
    (θ : BoundedRealSequence) (S : Finset ℕ) (z : ℂ) : ℂ :=
  ∑' n : {n // n ∉ S}, movingCanonicalRegularizedAtom θ n z

theorem movingCanonicalZero_ne_upper
    (θ : BoundedRealSequence) (n : ℕ) {z : ℂ}
    (hz : 0 < z.im) :
    z ≠ (movingCanonicalZero θ n : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.ofReal_im] at him
  linarith

theorem summable_movingCanonicalComplementCarrier
    (θ : BoundedRealSequence) (S : Finset ℕ) {z : ℂ}
    (hz : 0 < z.im) :
    Summable (fun n : {n // n ∉ S} =>
      movingCanonicalRegularizedAtom θ n z) := by
  have hfull := summable_movingCanonicalLogDerivative θ
    (fun n => movingCanonicalZero_ne_upper θ n hz)
  exact hfull.comp_injective Subtype.val_injective

theorem regularizedRealAtom_pick
    (a : ℝ) (z w : ℂ)
    (hz : 0 < z.im) (hw : 0 < w.im) :
    ((((a : ℂ) - z)⁻¹ - (a : ℂ)⁻¹) -
        star (((a : ℂ) - w)⁻¹ - (a : ℂ)⁻¹)) /
        (z - star w) =
      ((a : ℂ) - z)⁻¹ *
        star (((a : ℂ) - w)⁻¹) := by
  have haz : (a : ℂ) - z ≠ 0 := by
    intro h
    have him : -z.im = 0 := by
      simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub,
        Complex.zero_im] using congrArg Complex.im h
    linarith
  have haw : (a : ℂ) - w ≠ 0 := by
    intro h
    have him : -w.im = 0 := by
      simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub,
        Complex.zero_im] using congrArg Complex.im h
    linarith
  have hzw : z - star w ≠ 0 := by
    intro h
    have him : z.im + w.im = 0 := by
      simpa only [Complex.sub_im, Complex.star_def,
        Complex.conj_im, sub_neg_eq_add,
        Complex.zero_im] using congrArg Complex.im h
    linarith
  have hgram := GaloisForLFunctions.pick_gram_eq_kernel
    (t := fun _ : Fin 1 => a) z w
    (fun _ => haz) (fun _ => haw) hzw
  calc
    _ = (((a : ℂ) - z)⁻¹ -
          star (((a : ℂ) - w)⁻¹)) /
          (z - star w) := by
        congr 1
        simp only [star_sub, star_inv₀, Complex.star_def,
          Complex.conj_ofReal]
        ring
    _ = _ := by
      simpa using hgram.symm

theorem carrierPickMatrix_movingCanonicalComplementCarrier_eq_gram
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {N : ℕ} (z : Fin N → ℂ)
    (hz : ∀ j, 0 < (z j).im) :
    carrierPickMatrix (movingCanonicalComplementCarrier θ S) z =
      Matrix.of (fun j l =>
        ∑' n : {n // n ∉ S},
          (((movingCanonicalZero θ n.1 : ℂ) - z j)⁻¹ *
            star (((movingCanonicalZero θ n.1 : ℂ) - z l)⁻¹))) := by
  ext j l
  rw [carrierPickMatrix, Matrix.of_apply, Matrix.of_apply]
  have hj := summable_movingCanonicalComplementCarrier
    θ S (hz j)
  have hl := summable_movingCanonicalComplementCarrier
    θ S (hz l)
  have hdiff : Summable (fun n : {n // n ∉ S} =>
      movingCanonicalRegularizedAtom θ n (z j) -
        star (movingCanonicalRegularizedAtom θ n (z l))) :=
    hj.sub hl.star
  rw [movingCanonicalComplementCarrier,
    movingCanonicalComplementCarrier, tsum_star,
    ← hj.tsum_sub hl.star]
  rw [div_eq_mul_inv, ← hdiff.tsum_mul_right]
  apply tsum_congr
  intro n
  rw [← div_eq_mul_inv]
  exact regularizedRealAtom_pick
    (movingCanonicalZero θ n.1) (z j) (z l) (hz j) (hz l)

theorem movingCanonicalComplementCarrier_pick_posSemidef
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {N : ℕ} (z : Fin N → ℂ)
    (hz : ∀ j, 0 < (z j).im) :
    (carrierPickMatrix
      (movingCanonicalComplementCarrier θ S) z).PosSemidef := by
  rw [carrierPickMatrix_movingCanonicalComplementCarrier_eq_gram
    θ S z hz]
  apply tsum_outer_posSemidef
  intro j l
  have hj := summable_movingCanonicalComplementCarrier
    θ S (hz j)
  have hl := summable_movingCanonicalComplementCarrier
    θ S (hz l)
  have hdiff : Summable (fun n : {n // n ∉ S} =>
      movingCanonicalRegularizedAtom θ n (z j) -
        star (movingCanonicalRegularizedAtom θ n (z l))) :=
    hj.sub hl.star
  refine (hdiff.div_const (z j - star (z l))).congr
    (fun n => ?_)
  exact regularizedRealAtom_pick
    (movingCanonicalZero θ n.1) (z j) (z l) (hz j) (hz l)

theorem movingCanonicalComplementCarrier_eq_sub_sum
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    movingCanonicalComplementCarrier θ S z =
      movingCanonicalLogDerivative θ z -
        ∑ n ∈ S, movingCanonicalRegularizedAtom θ n z := by
  have hfull := summable_movingCanonicalLogDerivative θ
    (fun n => movingCanonicalZero_ne_upper θ n hz)
  have hsplit := hfull.sum_add_tsum_subtype_compl S
  change
    (∑ n ∈ S, movingCanonicalRegularizedAtom θ n z) +
        movingCanonicalComplementCarrier θ S z =
      movingCanonicalLogDerivative θ z at hsplit
  rw [add_comm] at hsplit
  exact eq_sub_of_add_eq hsplit

theorem continuousAt_movingCanonicalComplementCarrier
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {t : ℂ} (ht : 0 < t.im) :
    ContinuousAt (movingCanonicalComplementCarrier θ S) t := by
  have hfull : ContinuousAt
      (movingCanonicalLogDerivative θ) t :=
    (analyticAt_movingCanonicalLogDerivative θ ht).continuousAt
  have hfinite : ContinuousAt
      (fun w : ℂ =>
        ∑ n ∈ S, movingCanonicalRegularizedAtom θ n w) t := by
    have hatom : ∀ n : ℕ, ContinuousAt
        (movingCanonicalRegularizedAtom θ n) t := by
      intro n
      change ContinuousAt
        (fun w : ℂ =>
          ((movingCanonicalZero θ n : ℂ) - w)⁻¹ -
            (movingCanonicalZero θ n : ℂ)⁻¹) t
      apply ContinuousAt.sub
      · exact (continuousAt_const.sub continuousAt_id).inv₀
          (sub_ne_zero.mpr
            (Ne.symm (movingCanonicalZero_ne_upper θ n ht)))
      · exact continuousAt_const
    induction S using Finset.induction_on with
    | empty =>
        simpa using
          (continuousAt_const :
            ContinuousAt (fun _ : ℂ => (0 : ℂ)) t)
    | @insert n S hn ih =>
        have h := (hatom n).add ih
        change ContinuousAt
          (fun w =>
            movingCanonicalRegularizedAtom θ n w +
              ∑ m ∈ S,
                movingCanonicalRegularizedAtom θ m w) t at h
        simpa only [Finset.sum_insert hn] using h
  have hopen : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hu : {w : ℂ | 0 < w.im} ∈ 𝓝 t :=
    hopen.mem_nhds ht
  have heq :
      movingCanonicalComplementCarrier θ S =ᶠ[𝓝 t]
        fun w => movingCanonicalLogDerivative θ w -
          ∑ n ∈ S, movingCanonicalRegularizedAtom θ n w := by
    filter_upwards [hu] with w hw
    exact movingCanonicalComplementCarrier_eq_sub_sum θ S hw
  exact (hfull.sub hfinite).congr heq.symm

def movingCanonicalSurgerySelectedIndices
    {k : ℕ} (aIdx bIdx : Fin k → ℕ) : Finset ℕ :=
  Finset.univ.image aIdx ∪ Finset.univ.image bIdx

def movingCanonicalSurgeryConstant
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) : ℝ :=
  ∑ i, ((movingCanonicalZero θ (aIdx i))⁻¹ +
    (movingCanonicalZero θ (bIdx i))⁻¹)

def movingCanonicalSurgeryCarrier
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) : ℂ :=
  movingCanonicalComplementCarrier θ
      (movingCanonicalSurgerySelectedIndices aIdx bIdx) z +
    multiPairCarrier t z -
      (movingCanonicalSurgeryConstant θ aIdx bIdx : ℂ)

theorem carrierPickMatrix_sub_real_const
    {N : ℕ} (f : ℂ → ℂ) (c : ℝ)
    (z : Fin N → ℂ) :
    carrierPickMatrix (fun w => f w - (c : ℂ)) z =
      carrierPickMatrix f z := by
  ext j l
  simp only [carrierPickMatrix, Matrix.of_apply, star_sub,
    Complex.star_def, Complex.conj_ofReal]
  ring

theorem carrierPickMatrix_movingCanonicalSurgeryCarrier
    {k N : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : Fin N → ℂ) :
    carrierPickMatrix
        (movingCanonicalSurgeryCarrier θ aIdx bIdx t) z =
      carrierPickMatrix
        (fun w =>
          movingCanonicalComplementCarrier θ
              (movingCanonicalSurgerySelectedIndices aIdx bIdx) w +
            multiPairCarrier t w) z := by
  change carrierPickMatrix
      (fun w =>
        (movingCanonicalComplementCarrier θ
            (movingCanonicalSurgerySelectedIndices aIdx bIdx) w +
          multiPairCarrier t w) -
            (movingCanonicalSurgeryConstant θ aIdx bIdx : ℂ)) z =
    _
  exact carrierPickMatrix_sub_real_const _ _ z

theorem movingCanonicalSurgeryCarrier_exact_negativeSquares
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t) :
    (∀ {N : ℕ} (z : Fin N → ℂ),
      (∀ j, 0 < (z j).im) →
      (∀ i j, z j ≠ t i) →
      ∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ x ∈ W, x ≠ 0 →
          (star x ⬝ᵥ
            (carrierPickMatrix
              (movingCanonicalSurgeryCarrier
                θ aIdx bIdx t) z).mulVec x).re < 0) →
        Module.finrank ℂ W ≤ k) ∧
      ∃ z : Fin k → ℂ,
        (∀ j, 0 < (z j).im) ∧
        (∀ i j, z j ≠ t i) ∧
        Function.Injective z ∧
        ∀ x : Fin k → ℂ, x ≠ 0 →
          (star x ⬝ᵥ
            (carrierPickMatrix
              (movingCanonicalSurgeryCarrier
                θ aIdx bIdx t) z).mulVec x).re < 0 := by
  let S := movingCanonicalSurgerySelectedIndices aIdx bIdx
  have hcore := add_multiPairCarrier_exact_negativeSquares
    (movingCanonicalComplementCarrier θ S) t ht htinj
    (fun i => continuousAt_movingCanonicalComplementCarrier
      θ S (ht i))
    (fun {_} z hz =>
      movingCanonicalComplementCarrier_pick_posSemidef
        θ S z hz)
  constructor
  · intro N z hz hzt W hW
    apply hcore.1 z hz hzt W
    intro x hx hx0
    have hneg := hW x hx hx0
    rw [carrierPickMatrix_movingCanonicalSurgeryCarrier] at hneg
    exact hneg
  · obtain ⟨z, hz, hzt, hinj, hneg⟩ := hcore.2
    refine ⟨z, hz, hzt, hinj, ?_⟩
    intro x hx0
    have h := hneg x hx0
    rw [← carrierPickMatrix_movingCanonicalSurgeryCarrier
      θ aIdx bIdx t z] at h
    exact h

theorem neg_logDeriv_canonicalProductE1Indexed_eq
    {ι : Type*} (a : ι → ℂ)
    (ha : ∀ i, a i ≠ 0)
    (hsum : Summable (fun i => 1 / ‖a i‖ ^ 2))
    {z : ℂ} (hz : ∀ i, z ≠ a i)
    (hcarrier : Summable (fun i =>
      (a i - z)⁻¹ - (a i)⁻¹)) :
    -logDeriv (RHTower.canonicalProductE1Indexed a) z =
      ∑' i, ((a i - z)⁻¹ - (a i)⁻¹) := by
  have hfac : ∀ i,
      RHTower.weierstrassE1 (z / a i) ≠ 0 := by
    intro i
    rw [RHTower.weierstrassE1]
    apply mul_ne_zero
    · intro hzero
      have hdiv : z / a i = 1 :=
        (sub_eq_zero.mp hzero).symm
      apply hz i
      calc
        z = z / a i * a i :=
          (div_mul_cancel₀ z (ha i)).symm
        _ = a i := by rw [hdiv, one_mul]
    · exact Complex.exp_ne_zero _
  have hlogs : Summable (fun i =>
      logDeriv
        (fun w : ℂ =>
          RHTower.weierstrassE1 (w / a i)) z) := by
    apply hcarrier.neg.congr
    intro i
    have hd : a i - z ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hz i))
    have hinv : (a i - z)⁻¹ - (a i)⁻¹ =
        z / ((a i - z) * a i) := by
      simpa only [sub_sub_cancel] using
        inv_sub_inv hd (ha i)
    change -((a i - z)⁻¹ - (a i)⁻¹) =
      logDeriv
        (fun w : ℂ =>
          RHTower.weierstrassE1 (w / a i)) z
    rw [RHTower.logDeriv_weierstrassE1_div
      (ha i) (hz i)]
    rw [hinv, mul_comm (a i - z) (a i), ← neg_div]
  have hprod :
      RHTower.canonicalProductE1Indexed a z ≠ 0 :=
    RHTower.canonicalProductE1Indexed_ne_zero
      a ha hsum hz
  have hlog := logDeriv_tprod_eq_tsum
    isOpen_univ (Set.mem_univ z)
    hfac
    (by
      intro i
      simp only [RHTower.weierstrassE1]
      fun_prop)
    hlogs
    (RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      a ha hsum |>.multipliableLocallyUniformlyOn)
    hprod
  have hlog' :
      logDeriv
        (RHTower.canonicalProductE1Indexed a) z =
      ∑' i, logDeriv
        (fun w : ℂ =>
          RHTower.weierstrassE1 (w / a i)) z := by
    change logDeriv
      (fun w => ∏' i,
        RHTower.weierstrassE1 (w / a i)) z =
      ∑' i, logDeriv
        (fun w : ℂ =>
          RHTower.weierstrassE1 (w / a i)) z
    exact hlog
  rw [hlog', ← tsum_neg]
  apply tsum_congr
  intro i
  have hd : a i - z ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (hz i))
  have hinv : (a i - z)⁻¹ - (a i)⁻¹ =
      z / ((a i - z) * a i) := by
    simpa only [sub_sub_cancel] using
      inv_sub_inv hd (ha i)
  change
    -logDeriv
      (fun w : ℂ =>
        RHTower.weierstrassE1 (w / a i)) z =
      (a i - z)⁻¹ - (a i)⁻¹
  rw [RHTower.logDeriv_weierstrassE1_div
    (ha i) (hz i)]
  rw [hinv, mul_comm (a i - z) (a i),
    neg_div, neg_neg]

def movingCanonicalComplementProduct
    (θ : BoundedRealSequence) (S : Finset ℕ) :
    ℂ → ℂ :=
  RHTower.canonicalProductE1IndexedComplement
    (fun n => (movingCanonicalZero θ n : ℂ))
    (fun n => n ∈ S)

theorem movingCanonicalComplementProduct_analytic
    (θ : BoundedRealSequence) (S : Finset ℕ) :
    AnalyticOnNhd ℂ
      (movingCanonicalComplementProduct θ S) Set.univ := by
  exact
    RHTower.canonicalProductE1IndexedComplement_analytic
      (fun n => (movingCanonicalZero θ n : ℂ))
      (fun n => n ∈ S)
      (fun n => Complex.ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ n)))
      (summable_movingCanonicalZero_inv_sq θ)

theorem neg_logDeriv_movingCanonicalComplementProduct_eq
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    -logDeriv (movingCanonicalComplementProduct θ S) z =
      movingCanonicalComplementCarrier θ S z := by
  let a : {n // n ∉ S} → ℂ :=
    fun n => (movingCanonicalZero θ n.1 : ℂ)
  have ha : ∀ n, a n ≠ 0 :=
    fun n => Complex.ofReal_ne_zero.mpr
      (ne_of_gt (movingCanonicalZero_pos θ n.1))
  have hsum : Summable
      (fun n : {n // n ∉ S} =>
        1 / ‖a n‖ ^ 2) :=
    RHTower.canonicalProductE1IndexedComplement_inv_sq_summable
      (fun n => (movingCanonicalZero θ n : ℂ))
      (fun n => n ∈ S)
      (summable_movingCanonicalZero_inv_sq θ)
  have hpole : ∀ n, z ≠ a n :=
    fun n => movingCanonicalZero_ne_upper θ n.1 hz
  have hcarrier :
      Summable (fun n : {n // n ∉ S} =>
        (a n - z)⁻¹ - (a n)⁻¹) := by
    simpa [a, movingCanonicalRegularizedAtom] using
      summable_movingCanonicalComplementCarrier θ S hz
  simpa [movingCanonicalComplementProduct,
    RHTower.canonicalProductE1IndexedComplement,
    movingCanonicalComplementCarrier,
    movingCanonicalRegularizedAtom, a] using
      neg_logDeriv_canonicalProductE1Indexed_eq
        a ha hsum hpole hcarrier

def movingCanonicalSurgeryPairFactor
    (a b : ℝ) (t z : ℂ) : ℂ :=
  Complex.exp (z / (a : ℂ) + z / (b : ℂ)) /
      ((a : ℂ) * (b : ℂ)) *
    (z - t) * (z - star t)

def movingCanonicalSurgeryProduct
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) : ℂ :=
  movingCanonicalComplementProduct θ
      (movingCanonicalSurgerySelectedIndices aIdx bIdx) z *
    ∏ i, movingCanonicalSurgeryPairFactor
      (movingCanonicalZero θ (aIdx i))
      (movingCanonicalZero θ (bIdx i))
      (t i) z

theorem movingCanonicalSurgeryPairFactor_analytic
    (a b : ℝ) (t : ℂ) :
    AnalyticOnNhd ℂ
      (movingCanonicalSurgeryPairFactor a b t) Set.univ := by
  intro z hz
  change AnalyticAt ℂ
    (fun w =>
      Complex.exp (w / (a : ℂ) + w / (b : ℂ)) /
          ((a : ℂ) * (b : ℂ)) *
        (w - t) * (w - star t)) z
  fun_prop

theorem movingCanonicalSurgeryProduct_analytic
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    AnalyticOnNhd ℂ
      (movingCanonicalSurgeryProduct
        θ aIdx bIdx t) Set.univ := by
  apply AnalyticOnNhd.mul
  · exact movingCanonicalComplementProduct_analytic θ _
  · intro z hz
    let f : Fin k → ℂ → ℂ := fun i =>
      movingCanonicalSurgeryPairFactor
        (movingCanonicalZero θ (aIdx i))
        (movingCanonicalZero θ (bIdx i))
        (t i)
    change AnalyticAt ℂ (fun w => ∏ i, f i w) z
    have hfac : ∀ i, AnalyticAt ℂ (f i) z :=
      fun i => movingCanonicalSurgeryPairFactor_analytic
        _ _ _ z (Set.mem_univ z)
    induction (Finset.univ : Finset (Fin k))
        using Finset.induction_on with
    | empty =>
        simpa using
          (analyticAt_const (𝕜 := ℂ) (x := z) (v := (1 : ℂ)))
    | @insert i s hi ih =>
        have h := (hfac i).mul ih
        change AnalyticAt ℂ
          (fun w => f i w * ∏ j ∈ s, f j w) z at h
        simpa only [Finset.prod_insert hi] using h

theorem logDeriv_exp_linear'
    (c z : ℂ) :
    logDeriv (fun w => Complex.exp (c * w)) z = c := by
  have hf : DifferentiableAt ℂ
      (fun w : ℂ => c * w) z :=
    differentiableAt_id.const_mul c
  have hderiv :
      deriv (fun w : ℂ => c * w) z = c := by
    rw [deriv_const_mul _ differentiableAt_id,
      deriv_id'', mul_one]
  rw [show (fun w => Complex.exp (c * w)) =
      Complex.exp ∘ (fun w => c * w) from rfl,
    logDeriv_comp (g := fun w : ℂ => c * w)
      Complex.differentiableAt_exp hf,
    Complex.logDeriv_exp, Pi.one_apply, one_mul,
    hderiv]

theorem logDeriv_sub_const'
    (t z : ℂ) :
    logDeriv (fun w : ℂ => w - t) z =
      (z - t)⁻¹ := by
  rw [logDeriv_apply]
  have hd : deriv (fun w : ℂ => w - t) z = 1 := by
    rw [deriv_sub_const, deriv_id'']
  rw [hd, one_div]

theorem neg_logDeriv_movingCanonicalSurgeryPairFactor
    (a b : ℝ) (t z : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hzt : z ≠ t) (hzstar : z ≠ star t) :
    -logDeriv
        (movingCanonicalSurgeryPairFactor a b t) z =
      (t - z)⁻¹ + (star t - z)⁻¹ -
        ((a : ℂ)⁻¹ + (b : ℂ)⁻¹) := by
  let E : ℂ → ℂ := fun w =>
    Complex.exp
      (((a : ℂ)⁻¹ + (b : ℂ)⁻¹) * w)
  have hEeq : (fun w : ℂ =>
      Complex.exp (w / (a : ℂ) + w / (b : ℂ)) /
        ((a : ℂ) * (b : ℂ))) =
      fun w =>
        (((a : ℂ) * (b : ℂ))⁻¹) * E w := by
    funext w
    dsimp only [E]
    rw [div_eq_mul_inv]
    have hexp :
        w / (a : ℂ) + w / (b : ℂ) =
          ((a : ℂ)⁻¹ + (b : ℂ)⁻¹) * w := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hexp]
    ring
  have hab : ((a : ℂ) * (b : ℂ)) ≠ 0 :=
    mul_ne_zero
      (Complex.ofReal_ne_zero.mpr ha)
      (Complex.ofReal_ne_zero.mpr hb)
  have hEne : E z ≠ 0 := Complex.exp_ne_zero _
  have hEdiff : DifferentiableAt ℂ E z := by
    dsimp only [E]
    fun_prop
  have hbaseNe :
      (((a : ℂ) * (b : ℂ))⁻¹) * E z ≠ 0 :=
    mul_ne_zero (inv_ne_zero hab) hEne
  have hbaseDiff : DifferentiableAt ℂ
      (fun w =>
        (((a : ℂ) * (b : ℂ))⁻¹) * E w) z :=
    by fun_prop
  change -logDeriv
      (fun w =>
        (Complex.exp
            (w / (a : ℂ) + w / (b : ℂ)) /
              ((a : ℂ) * (b : ℂ)) *
            (w - t)) *
          (w - star t)) z = _
  rw [show
      (fun w =>
        (Complex.exp
            (w / (a : ℂ) + w / (b : ℂ)) /
              ((a : ℂ) * (b : ℂ)) *
            (w - t)) *
          (w - star t)) =
        (fun w =>
          ((((a : ℂ) * (b : ℂ))⁻¹) * E w *
            (w - t)) * (w - star t)) by
      funext w
      rw [congrFun hEeq w]]
  rw [logDeriv_mul
      (f := fun w =>
        (((a : ℂ) * (b : ℂ))⁻¹) * E w *
          (w - t))
      (g := fun w => w - star t) z
      (mul_ne_zero hbaseNe
        (sub_ne_zero.mpr hzt))
      (sub_ne_zero.mpr hzstar)
      (hbaseDiff.mul
        (differentiableAt_id.sub_const t))
      (differentiableAt_id.sub_const (star t)),
    logDeriv_mul
      (f := fun w =>
        (((a : ℂ) * (b : ℂ))⁻¹) * E w)
      (g := fun w => w - t) z hbaseNe
      (sub_ne_zero.mpr hzt)
      hbaseDiff
      (differentiableAt_id.sub_const t),
    logDeriv_const_mul z
      (((a : ℂ) * (b : ℂ))⁻¹)
      (inv_ne_zero hab),
    logDeriv_exp_linear',
    logDeriv_sub_const', logDeriv_sub_const']
  have htneg : t - z = -(z - t) := by ring
  have hsneg : star t - z = -(z - star t) := by ring
  rw [htneg, hsneg, inv_neg, inv_neg]
  ring

theorem neg_logDeriv_movingCanonicalSurgeryProduct_eq
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    {z : ℂ} (hz : 0 < z.im)
    (ht : ∀ i, 0 < (t i).im)
    (hzt : ∀ i, z ≠ t i) :
    -logDeriv
        (movingCanonicalSurgeryProduct
          θ aIdx bIdx t) z =
      movingCanonicalSurgeryCarrier
        θ aIdx bIdx t z := by
  let S :=
    movingCanonicalSurgerySelectedIndices aIdx bIdx
  let P : ℂ → ℂ := fun w =>
    ∏ i, movingCanonicalSurgeryPairFactor
      (movingCanonicalZero θ (aIdx i))
      (movingCanonicalZero θ (bIdx i))
      (t i) w
  have hcompNe :
      movingCanonicalComplementProduct θ S z ≠ 0 := by
    apply
      RHTower.canonicalProductE1IndexedComplement_ne_zero
        (fun n =>
          (movingCanonicalZero θ n : ℂ))
        (fun n => n ∈ S)
        (fun n => Complex.ofReal_ne_zero.mpr
          (ne_of_gt
            (movingCanonicalZero_pos θ n)))
        (summable_movingCanonicalZero_inv_sq θ)
    intro n
    exact movingCanonicalZero_ne_upper θ n.1 hz
  have hzstar : ∀ i, z ≠ star (t i) := by
    intro i h
    have him := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith [ht i]
  have hpairNe : ∀ i,
      movingCanonicalSurgeryPairFactor
        (movingCanonicalZero θ (aIdx i))
        (movingCanonicalZero θ (bIdx i))
        (t i) z ≠ 0 := by
    intro i
    simp only [movingCanonicalSurgeryPairFactor]
    exact mul_ne_zero
      (mul_ne_zero
        (div_ne_zero (Complex.exp_ne_zero _)
          (mul_ne_zero
            (Complex.ofReal_ne_zero.mpr
              (ne_of_gt
                (movingCanonicalZero_pos θ
                  (aIdx i))))
            (Complex.ofReal_ne_zero.mpr
              (ne_of_gt
                (movingCanonicalZero_pos θ
                  (bIdx i))))))
        (sub_ne_zero.mpr (hzt i)))
      (sub_ne_zero.mpr (hzstar i))
  have hPNe : P z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact hpairNe i
  have hcompDiff : DifferentiableAt ℂ
      (movingCanonicalComplementProduct θ S) z :=
    (movingCanonicalComplementProduct_analytic θ S
      z (Set.mem_univ z)).differentiableAt
  have hPDiff : DifferentiableAt ℂ P z := by
    dsimp only [P]
    apply DifferentiableAt.fun_finsetProd
    intro i hi
    exact
      (movingCanonicalSurgeryPairFactor_analytic
        _ _ _ z (Set.mem_univ z)).differentiableAt
  change -logDeriv
      (fun w =>
        movingCanonicalComplementProduct θ S w *
          P w) z = _
  rw [logDeriv_mul z hcompNe hPNe
    hcompDiff hPDiff]
  have hcomp :=
    neg_logDeriv_movingCanonicalComplementProduct_eq
      θ S hz
  have hprod :
      logDeriv P z =
        ∑ i, logDeriv
          (movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx i))
            (movingCanonicalZero θ (bIdx i))
            (t i)) z := by
    dsimp only [P]
    exact logDeriv_prod
      (fun i _ => hpairNe i)
      (fun i _ =>
        (movingCanonicalSurgeryPairFactor_analytic
          _ _ _ z
          (Set.mem_univ z)).differentiableAt)
  rw [hprod]
  have hpair : ∀ i,
      -logDeriv
          (movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx i))
            (movingCanonicalZero θ (bIdx i))
            (t i)) z =
        (t i - z)⁻¹ + (star (t i) - z)⁻¹ -
          (((movingCanonicalZero θ (aIdx i) : ℂ)⁻¹) +
            ((movingCanonicalZero θ (bIdx i) : ℂ)⁻¹)) :=
    fun i =>
      neg_logDeriv_movingCanonicalSurgeryPairFactor
        _ _ _ _
        (ne_of_gt
          (movingCanonicalZero_pos θ (aIdx i)))
        (ne_of_gt
          (movingCanonicalZero_pos θ (bIdx i)))
        (hzt i) (hzstar i)
  have hpairsum :
      -(∑ i, logDeriv
          (movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx i))
            (movingCanonicalZero θ (bIdx i))
            (t i)) z) =
        multiPairCarrier t z -
          (movingCanonicalSurgeryConstant
            θ aIdx bIdx : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    simp_rw [hpair]
    rw [multiPairCarrier,
      movingCanonicalSurgeryConstant]
    push_cast
    rw [Finset.sum_sub_distrib]
  rw [movingCanonicalSurgeryCarrier]
  linear_combination hcomp + hpairsum

def movingCanonicalSurgeryIndexFamily
    {k : ℕ} (aIdx bIdx : Fin k → ℕ) :
    Fin k ⊕ Fin k → ℕ :=
  Sum.elim aIdx bIdx

theorem movingCanonicalSurgerySelectedIndices_eq_range
    {k : ℕ} (aIdx bIdx : Fin k → ℕ) :
    {n : ℕ |
      n ∈ movingCanonicalSurgerySelectedIndices
        aIdx bIdx} =
      Set.range
        (movingCanonicalSurgeryIndexFamily
          aIdx bIdx) := by
  ext n
  simp only [movingCanonicalSurgerySelectedIndices,
    movingCanonicalSurgeryIndexFamily,
    Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and, Set.mem_setOf_eq,
    Set.mem_range]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩
  · rintro ⟨i, rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr i => exact Or.inr ⟨i, rfl⟩

theorem movingCanonicalSelectedProduct_eq_pairProduct
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ)
    (hidx : Function.Injective
      (movingCanonicalSurgeryIndexFamily aIdx bIdx))
    (z : ℂ) :
    RHTower.canonicalProductE1IndexedSelected
        (fun n => (movingCanonicalZero θ n : ℂ))
        (fun n =>
          n ∈ movingCanonicalSurgerySelectedIndices
            aIdx bIdx) z =
      ∏ i,
        (RHTower.weierstrassE1
            (z /
              (movingCanonicalZero θ (aIdx i) : ℂ)) *
          RHTower.weierstrassE1
            (z /
              (movingCanonicalZero θ (bIdx i) : ℂ))) := by
  let u : Fin k ⊕ Fin k → ℕ :=
    movingCanonicalSurgeryIndexFamily aIdx bIdx
  let erange :
      (Fin k ⊕ Fin k) ≃ Set.range u :=
    Equiv.ofInjective u hidx
  let eset :
      Set.range u ≃
        ↥(movingCanonicalSurgerySelectedIndices
          aIdx bIdx) :=
    { toFun := fun n =>
        ⟨n.1, by
          have hn :
              n.1 ∈
                {m : ℕ |
                  m ∈
                    movingCanonicalSurgerySelectedIndices
                      aIdx bIdx} := by
            rw [movingCanonicalSurgerySelectedIndices_eq_range
              aIdx bIdx]
            exact n.2
          exact hn⟩
      invFun := fun n =>
        ⟨n.1, by
          rw [←
            movingCanonicalSurgerySelectedIndices_eq_range
              aIdx bIdx]
          exact n.2⟩
      left_inv := by
        intro n
        apply Subtype.ext
        rfl
      right_inv := by
        intro n
        apply Subtype.ext
        rfl }
  let e := erange.trans eset
  have heval (q : Fin k ⊕ Fin k) :
      (e q).1 = u q := by
    dsimp only [e, Equiv.trans_apply, eset, erange]
    rw [Equiv.ofInjective_apply]
    rfl
  rw [RHTower.canonicalProductE1IndexedSelected,
    RHTower.canonicalProductE1Indexed]
  rw [← e.tprod_eq]
  rw [tprod_fintype, Fintype.prod_sum_type]
  simp_rw [heval]
  rw [Finset.prod_mul_distrib]
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_congr
    intro i
    change
      RHTower.weierstrassE1
          (z /
            (movingCanonicalZero θ (aIdx i) : ℂ)) =
        RHTower.weierstrassE1
          (z /
            (movingCanonicalZero θ (aIdx i) : ℂ))
    rfl
  · apply Fintype.prod_congr
    intro i
    change
      RHTower.weierstrassE1
          (z /
            (movingCanonicalZero θ (bIdx i) : ℂ)) =
        RHTower.weierstrassE1
          (z /
            (movingCanonicalZero θ (bIdx i) : ℂ))
    rfl

theorem movingCanonicalProduct_eq_selected_mul_complement
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (z : ℂ) :
    movingCanonicalProduct θ z =
      RHTower.canonicalProductE1IndexedSelected
          (fun n => (movingCanonicalZero θ n : ℂ))
          (fun n =>
            n ∈ movingCanonicalSurgerySelectedIndices
              aIdx bIdx) z *
        movingCanonicalComplementProduct θ
          (movingCanonicalSurgerySelectedIndices
            aIdx bIdx) z := by
  exact
    RHTower.canonicalProductE1Indexed_eq_selected_mul_complement
      (fun n => (movingCanonicalZero θ n : ℂ))
      (fun n =>
        n ∈ movingCanonicalSurgerySelectedIndices
          aIdx bIdx)
      (fun n => Complex.ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ n)))
      (summable_movingCanonicalZero_inv_sq θ) z

theorem weierstrassPair_mul_surgeryQuotient
    (a b : ℝ) (t z : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hza : z ≠ (a : ℂ))
    (hzb : z ≠ (b : ℂ)) :
    (RHTower.weierstrassE1 (z / (a : ℂ)) *
        RHTower.weierstrassE1 (z / (b : ℂ))) *
      (((z - t) * (z - star t)) /
        ((z - (a : ℂ)) * (z - (b : ℂ)))) =
      movingCanonicalSurgeryPairFactor a b t z := by
  rw [RHTower.weierstrassE1,
    RHTower.weierstrassE1,
    movingCanonicalSurgeryPairFactor]
  rw [Complex.exp_add]
  field_simp [Complex.ofReal_ne_zero.mpr ha,
    Complex.ofReal_ne_zero.mpr hb,
    sub_ne_zero.mpr hza,
    sub_ne_zero.mpr hzb]
  ring

theorem movingCanonicalSurgeryProduct_eq_paperQuotient
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (hidx : Function.Injective
      (movingCanonicalSurgeryIndexFamily aIdx bIdx))
    {z : ℂ}
    (hza : ∀ i,
      z ≠ (movingCanonicalZero θ (aIdx i) : ℂ))
    (hzb : ∀ i,
      z ≠ (movingCanonicalZero θ (bIdx i) : ℂ)) :
    movingCanonicalSurgeryProduct
        θ aIdx bIdx t z =
      movingCanonicalProduct θ z *
        ∏ i,
          (((z - t i) * (z - star (t i))) /
            ((z -
                (movingCanonicalZero θ (aIdx i) : ℂ)) *
              (z -
                (movingCanonicalZero θ (bIdx i) : ℂ)))) := by
  let S :=
    movingCanonicalSurgerySelectedIndices aIdx bIdx
  let A : Fin k → ℂ := fun i =>
    RHTower.weierstrassE1
        (z /
          (movingCanonicalZero θ (aIdx i) : ℂ)) *
      RHTower.weierstrassE1
        (z /
          (movingCanonicalZero θ (bIdx i) : ℂ))
  let R : Fin k → ℂ := fun i =>
    ((z - t i) * (z - star (t i))) /
      ((z -
          (movingCanonicalZero θ (aIdx i) : ℂ)) *
        (z -
          (movingCanonicalZero θ (bIdx i) : ℂ)))
  have hsplit :=
    movingCanonicalProduct_eq_selected_mul_complement
      θ aIdx bIdx z
  have hselected :=
    movingCanonicalSelectedProduct_eq_pairProduct
      θ aIdx bIdx hidx z
  have hpair : ∀ i,
      A i * R i =
        movingCanonicalSurgeryPairFactor
          (movingCanonicalZero θ (aIdx i))
          (movingCanonicalZero θ (bIdx i))
          (t i) z := by
    intro i
    exact weierstrassPair_mul_surgeryQuotient
      _ _ _ _
      (ne_of_gt
        (movingCanonicalZero_pos θ (aIdx i)))
      (ne_of_gt
        (movingCanonicalZero_pos θ (bIdx i)))
      (hza i) (hzb i)
  have hpairProd :
      ∏ i, movingCanonicalSurgeryPairFactor
          (movingCanonicalZero θ (aIdx i))
          (movingCanonicalZero θ (bIdx i))
          (t i) z =
        (∏ i, A i) * ∏ i, R i := by
    rw [← Finset.prod_mul_distrib]
    apply Fintype.prod_congr
    intro i
    exact (hpair i).symm
  rw [movingCanonicalSurgeryProduct, hpairProd]
  change
    movingCanonicalComplementProduct θ S z *
        ((∏ i, A i) * ∏ i, R i) =
      movingCanonicalProduct θ z * ∏ i, R i
  rw [hsplit, hselected]
  change
    movingCanonicalComplementProduct θ S z *
        ((∏ i, A i) * ∏ i, R i) =
      ((∏ i, A i) *
        movingCanonicalComplementProduct θ S z) *
          ∏ i, R i
  ring

theorem movingCanonicalComplementProduct_eq_zero_iff
    (θ : BoundedRealSequence) (S : Finset ℕ)
    (z : ℂ) :
    movingCanonicalComplementProduct θ S z = 0 ↔
      ∃ n : ℕ, n ∉ S ∧
        z = (movingCanonicalZero θ n : ℂ) := by
  constructor
  · intro hzero
    by_contra hnone
    have haway :
        ∀ n : {n // n ∉ S},
          z ≠ (movingCanonicalZero θ n.1 : ℂ) := by
      intro n hn
      exact hnone ⟨n.1, n.2, hn⟩
    exact
      (RHTower.canonicalProductE1IndexedComplement_ne_zero
        (fun n =>
          (movingCanonicalZero θ n : ℂ))
        (fun n => n ∈ S)
        (fun n => Complex.ofReal_ne_zero.mpr
          (ne_of_gt
            (movingCanonicalZero_pos θ n)))
        (summable_movingCanonicalZero_inv_sq θ)
        z haway) hzero
  · rintro ⟨n, hn, rfl⟩
    rw [movingCanonicalComplementProduct,
      RHTower.canonicalProductE1IndexedComplement,
      RHTower.canonicalProductE1Indexed]
    apply tprod_of_exists_eq_zero
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [RHTower.weierstrassE1,
      div_self
        (Complex.ofReal_ne_zero.mpr
          (ne_of_gt
            (movingCanonicalZero_pos θ n)))]
    simp

theorem movingCanonicalSurgeryPairFactor_eq_zero_iff
    (a b : ℝ) (t z : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    movingCanonicalSurgeryPairFactor a b t z = 0 ↔
      z = t ∨ z = star t := by
  rw [movingCanonicalSurgeryPairFactor]
  have hab :
      ((a : ℂ) * (b : ℂ)) ≠ 0 :=
    mul_ne_zero
      (Complex.ofReal_ne_zero.mpr ha)
      (Complex.ofReal_ne_zero.mpr hb)
  simp only [mul_eq_zero, div_eq_zero_iff,
    Complex.exp_ne_zero, hab,
    or_false, sub_eq_zero]
  tauto

theorem movingCanonicalSurgeryProduct_eq_zero_iff
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) :
    movingCanonicalSurgeryProduct
        θ aIdx bIdx t z = 0 ↔
      (∃ n : ℕ,
        n ∉ movingCanonicalSurgerySelectedIndices
          aIdx bIdx ∧
        z = (movingCanonicalZero θ n : ℂ)) ∨
      ∃ i : Fin k, z = t i ∨ z = star (t i) := by
  rw [movingCanonicalSurgeryProduct, mul_eq_zero]
  rw [movingCanonicalComplementProduct_eq_zero_iff]
  constructor
  · rintro (hcomp | hprod)
    · exact Or.inl hcomp
    · right
      rw [Finset.prod_eq_zero_iff] at hprod
      obtain ⟨i, hi, hzero⟩ := hprod
      exact ⟨i,
        (movingCanonicalSurgeryPairFactor_eq_zero_iff
          _ _ _ _
          (ne_of_gt
            (movingCanonicalZero_pos θ (aIdx i)))
          (ne_of_gt
            (movingCanonicalZero_pos θ (bIdx i)))).mp
          hzero⟩
  · rintro (hcomp | ⟨i, hi⟩)
    · exact Or.inl hcomp
    · right
      rw [Finset.prod_eq_zero_iff]
      exact ⟨i, Finset.mem_univ i,
        (movingCanonicalSurgeryPairFactor_eq_zero_iff
          _ _ _ _
          (ne_of_gt
            (movingCanonicalZero_pos θ (aIdx i)))
          (ne_of_gt
            (movingCanonicalZero_pos θ (bIdx i)))).mpr hi⟩

theorem analyticOrderAt_linear_sub
    (w : ℂ) :
    analyticOrderAt (fun z : ℂ => z - w) w = 1 := by
  have h : AnalyticAt ℂ
      (fun z : ℂ => z - w) w :=
    analyticAt_id.sub analyticAt_const
  have hc := h.analyticOrderAt_eq_natCast (n := 1)
  rw [Nat.cast_one] at hc
  rw [hc]
  exact
    ⟨fun _ => 1, analyticAt_const, one_ne_zero,
      by filter_upwards with z using by simp⟩

theorem analyticOrderAt_finsetProduct
    {ι : Type*} (z : ℂ) (s : Finset ι)
    (g : ι → ℂ → ℂ)
    (hg : ∀ i ∈ s, AnalyticAt ℂ (g i) z) :
    analyticOrderAt
        (fun w => ∏ i ∈ s, g i w) z =
      ∑ i ∈ s, analyticOrderAt (g i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact analyticOrderAt_eq_zero.mpr
        (Or.inr one_ne_zero)
  | @insert i s hi ih =>
      have hhead : AnalyticAt ℂ (g i) z :=
        hg i (Finset.mem_insert_self i s)
      have htail : AnalyticAt ℂ
          (fun w => ∏ j ∈ s, g j w) z := by
        have h := Finset.analyticAt_prod
          (𝕜 := ℂ) s
          (fun j hj =>
            hg j (Finset.mem_insert_of_mem hj))
        have heq :
            (∏ j ∈ s, g j) =
              fun w => ∏ j ∈ s, g j w := by
          funext w
          rw [Finset.prod_apply]
        rwa [heq] at h
      have hfun :
          (fun w => ∏ j ∈ insert i s, g j w) =
            fun w => g i w * ∏ j ∈ s, g j w := by
        funext w
        rw [Finset.prod_insert hi]
      rw [hfun]
      have hord :=
        analyticOrderAt_mul hhead htail
      change
        analyticOrderAt
            (fun w =>
              g i w * ∏ j ∈ s, g j w) z =
          analyticOrderAt (g i) z +
            analyticOrderAt
              (fun w => ∏ j ∈ s, g j w) z at hord
      rw [hord, Finset.sum_insert hi,
        ih (fun j hj =>
          hg j (Finset.mem_insert_of_mem hj))]

theorem movingCanonicalComplementProduct_zero_analyticOrderAt
    (θ : BoundedRealSequence) (S : Finset ℕ)
    (n : ℕ) (hn : n ∉ S) :
    analyticOrderAt
        (movingCanonicalComplementProduct θ S)
        (movingCanonicalZero θ n : ℂ) = 1 := by
  let selected : ℂ → ℂ :=
    RHTower.canonicalProductE1IndexedSelected
      (fun j => (movingCanonicalZero θ j : ℂ))
      (fun j => j ∈ S)
  have hselectedAn : AnalyticAt ℂ selected
      (movingCanonicalZero θ n : ℂ) :=
    RHTower.canonicalProductE1IndexedSelected_analytic
      (fun j => (movingCanonicalZero θ j : ℂ))
      (fun j => j ∈ S)
      (fun j => Complex.ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ j)))
      (summable_movingCanonicalZero_inv_sq θ)
      _ (Set.mem_univ _)
  have hselectedNe : selected
      (movingCanonicalZero θ n : ℂ) ≠ 0 := by
    apply
      RHTower.canonicalProductE1IndexedSelected_ne_zero
        (fun j =>
          (movingCanonicalZero θ j : ℂ))
        (fun j => j ∈ S)
        (fun j => Complex.ofReal_ne_zero.mpr
          (ne_of_gt
            (movingCanonicalZero_pos θ j)))
        (summable_movingCanonicalZero_inv_sq θ)
    intro j hzero
    have heq :
        movingCanonicalZero θ n =
          movingCanonicalZero θ j.1 :=
      Complex.ofReal_injective hzero
    have hnj : n = j.1 :=
      movingCanonicalZero_injective θ heq
    exact hn (hnj ▸ j.2)
  have hselectedOrder :
      analyticOrderAt selected
        (movingCanonicalZero θ n : ℂ) = 0 :=
    hselectedAn.analyticOrderAt_eq_zero.mpr
      hselectedNe
  have hcompAn : AnalyticAt ℂ
      (movingCanonicalComplementProduct θ S)
      (movingCanonicalZero θ n : ℂ) :=
    movingCanonicalComplementProduct_analytic θ S
      _ (Set.mem_univ _)
  have hfun : movingCanonicalProduct θ =
      fun z =>
        selected z *
          movingCanonicalComplementProduct θ S z := by
    funext z
    exact
      RHTower.canonicalProductE1Indexed_eq_selected_mul_complement
        (fun j =>
          (movingCanonicalZero θ j : ℂ))
        (fun j => j ∈ S)
        (fun j => Complex.ofReal_ne_zero.mpr
          (ne_of_gt
            (movingCanonicalZero_pos θ j)))
        (summable_movingCanonicalZero_inv_sq θ) z
  have hfull :=
    movingCanonicalProduct_zero_analyticOrderAt θ n
  rw [hfun] at hfull
  have hord :=
    analyticOrderAt_mul hselectedAn hcompAn
  change
    analyticOrderAt
        (fun z =>
          selected z *
            movingCanonicalComplementProduct θ S z)
        (movingCanonicalZero θ n : ℂ) =
      analyticOrderAt selected
          (movingCanonicalZero θ n : ℂ) +
        analyticOrderAt
          (movingCanonicalComplementProduct θ S)
          (movingCanonicalZero θ n : ℂ) at hord
  rw [hord, hselectedOrder, zero_add] at hfull
  exact hfull

theorem movingCanonicalSurgeryPairFactor_zero_analyticOrderAt
    (a b : ℝ) (t : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (htne : t ≠ star t) :
    analyticOrderAt
        (movingCanonicalSurgeryPairFactor a b t) t = 1 ∧
      analyticOrderAt
        (movingCanonicalSurgeryPairFactor a b t)
          (star t) = 1 := by
  let base : ℂ → ℂ := fun w =>
    Complex.exp (w / (a : ℂ) + w / (b : ℂ)) /
      ((a : ℂ) * (b : ℂ))
  have hab :
      ((a : ℂ) * (b : ℂ)) ≠ 0 :=
    mul_ne_zero
      (Complex.ofReal_ne_zero.mpr ha)
      (Complex.ofReal_ne_zero.mpr hb)
  have hbaseAn : ∀ z, AnalyticAt ℂ base z := by
    intro z
    dsimp only [base]
    fun_prop
  have hbaseNe : ∀ z, base z ≠ 0 := by
    intro z
    exact div_ne_zero (Complex.exp_ne_zero _) hab
  constructor
  · let unit : ℂ → ℂ := fun w =>
      base w * (w - star t)
    have hunitAn : AnalyticAt ℂ unit t :=
      (hbaseAn t).mul
        (analyticAt_id.sub analyticAt_const)
    have hunitNe : unit t ≠ 0 :=
      mul_ne_zero (hbaseNe t)
        (sub_ne_zero.mpr htne)
    have hunitOrder :
        analyticOrderAt unit t = 0 :=
      hunitAn.analyticOrderAt_eq_zero.mpr hunitNe
    have hlinAn : AnalyticAt ℂ
        (fun w : ℂ => w - t) t :=
      analyticAt_id.sub analyticAt_const
    have hord :=
      analyticOrderAt_mul hlinAn hunitAn
    have hfun :
        movingCanonicalSurgeryPairFactor a b t =
          fun w => (w - t) * unit w := by
      funext w
      rw [movingCanonicalSurgeryPairFactor]
      dsimp only [unit, base]
      ring
    rw [hfun]
    change
      analyticOrderAt
          (fun w => (w - t) * unit w) t = 1
    change
      analyticOrderAt
          (fun w => (w - t) * unit w) t =
        analyticOrderAt (fun w : ℂ => w - t) t +
          analyticOrderAt unit t at hord
    rw [hord, analyticOrderAt_linear_sub,
      hunitOrder, add_zero]
  · let unit : ℂ → ℂ := fun w =>
      base w * (w - t)
    have hunitAn : AnalyticAt ℂ unit (star t) :=
      (hbaseAn (star t)).mul
        (analyticAt_id.sub analyticAt_const)
    have hstarne : star t ≠ t := Ne.symm htne
    have hunitNe : unit (star t) ≠ 0 :=
      mul_ne_zero (hbaseNe (star t))
        (sub_ne_zero.mpr hstarne)
    have hunitOrder :
        analyticOrderAt unit (star t) = 0 :=
      hunitAn.analyticOrderAt_eq_zero.mpr hunitNe
    have hlinAn : AnalyticAt ℂ
        (fun w : ℂ => w - star t) (star t) :=
      analyticAt_id.sub analyticAt_const
    have hord :=
      analyticOrderAt_mul hunitAn hlinAn
    have hfun :
        movingCanonicalSurgeryPairFactor a b t =
          fun w => unit w * (w - star t) := by
      funext w
      rw [movingCanonicalSurgeryPairFactor]
    rw [hfun]
    change
      analyticOrderAt
          (fun w => unit w * (w - star t))
          (star t) = 1
    change
      analyticOrderAt
          (fun w => unit w * (w - star t))
          (star t) =
        analyticOrderAt unit (star t) +
          analyticOrderAt
            (fun w : ℂ => w - star t)
            (star t) at hord
    rw [hord, hunitOrder,
      analyticOrderAt_linear_sub, zero_add]

theorem movingCanonicalComplementProduct_ne_zero_of_im_ne_zero
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {z : ℂ} (hz : z.im ≠ 0) :
    movingCanonicalComplementProduct θ S z ≠ 0 := by
  rw [Ne, movingCanonicalComplementProduct_eq_zero_iff]
  rintro ⟨n, hn, hzero⟩
  apply hz
  rw [hzero]
  exact Complex.ofReal_im _

theorem movingCanonicalSurgeryPairProduct_analyticOrderAt
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) :
    analyticOrderAt
        (fun w =>
          ∏ i, movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx i))
            (movingCanonicalZero θ (bIdx i))
            (t i) w) z =
      ∑ i, analyticOrderAt
        (movingCanonicalSurgeryPairFactor
          (movingCanonicalZero θ (aIdx i))
          (movingCanonicalZero θ (bIdx i))
          (t i)) z := by
  apply analyticOrderAt_finsetProduct
  intro i hi
  exact movingCanonicalSurgeryPairFactor_analytic
    _ _ _ z (Set.mem_univ z)

theorem movingCanonicalSurgeryProduct_inserted_zero_analyticOrderAt
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t)
    (i : Fin k) :
    analyticOrderAt
        (movingCanonicalSurgeryProduct
          θ aIdx bIdx t) (t i) = 1 ∧
      analyticOrderAt
        (movingCanonicalSurgeryProduct
          θ aIdx bIdx t) (star (t i)) = 1 := by
  let S :=
    movingCanonicalSurgerySelectedIndices aIdx bIdx
  let g : Fin k → ℂ → ℂ := fun j =>
    movingCanonicalSurgeryPairFactor
      (movingCanonicalZero θ (aIdx j))
      (movingCanonicalZero θ (bIdx j))
      (t j)
  have htstar : ∀ j, t j ≠ star (t j) := by
    intro j h
    have him := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith [ht j]
  have hgAn : ∀ j z, AnalyticAt ℂ (g j) z :=
    fun j z =>
      movingCanonicalSurgeryPairFactor_analytic
        _ _ _ z (Set.mem_univ z)
  have hcompAn : ∀ z, AnalyticAt ℂ
      (movingCanonicalComplementProduct θ S) z :=
    fun z =>
      movingCanonicalComplementProduct_analytic θ S
        z (Set.mem_univ z)
  constructor
  · have hcompNe :
        movingCanonicalComplementProduct θ S (t i) ≠ 0 :=
      movingCanonicalComplementProduct_ne_zero_of_im_ne_zero
        θ S (ne_of_gt (ht i))
    have hcompOrder :
        analyticOrderAt
            (movingCanonicalComplementProduct θ S)
            (t i) = 0 :=
      (hcompAn (t i)).analyticOrderAt_eq_zero.mpr
        hcompNe
    have hgOrder : ∀ j, analyticOrderAt
        (g j) (t i) = if j = i then 1 else 0 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp
        exact
          (movingCanonicalSurgeryPairFactor_zero_analyticOrderAt
            _ _ _ (ne_of_gt
              (movingCanonicalZero_pos θ (aIdx i)))
            (ne_of_gt
              (movingCanonicalZero_pos θ (bIdx i)))
            (htstar i)).1
      · rw [if_neg hji]
        apply (hgAn j (t i)).analyticOrderAt_eq_zero.mpr
        change
          movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx j))
            (movingCanonicalZero θ (bIdx j))
            (t j) (t i) ≠ 0
        rw [Ne,
          movingCanonicalSurgeryPairFactor_eq_zero_iff
          _ _ _ _
          (ne_of_gt
            (movingCanonicalZero_pos θ (aIdx j)))
          (ne_of_gt
            (movingCanonicalZero_pos θ (bIdx j)))]
        rw [not_or]
        constructor
        · exact fun h => hji (htinj h).symm
        · intro h
          have him := congrArg Complex.im h
          simp only [Complex.star_def,
            Complex.conj_im] at him
          linarith [ht i, ht j]
    have hpairOrder :=
      movingCanonicalSurgeryPairProduct_analyticOrderAt
        θ aIdx bIdx t (t i)
    have hsum : (∑ j, analyticOrderAt
        (g j) (t i)) = 1 := by
      simp_rw [hgOrder]
      simp
    have hpairAn : AnalyticAt ℂ
        (fun w => ∏ j, g j w) (t i) := by
      have h := Finset.analyticAt_prod
        (𝕜 := ℂ) Finset.univ
        (fun j hj => hgAn j (t i))
      have heq : (∏ j, g j) =
          fun w => ∏ j, g j w := by
        funext w
        rw [Finset.prod_apply]
      rwa [heq] at h
    have hord := analyticOrderAt_mul
      (hcompAn (t i)) hpairAn
    change analyticOrderAt
        (fun w =>
          movingCanonicalComplementProduct θ S w *
            ∏ j, g j w) (t i) = 1
    change analyticOrderAt
        (fun w =>
          movingCanonicalComplementProduct θ S w *
            ∏ j, g j w) (t i) =
      analyticOrderAt
          (movingCanonicalComplementProduct θ S)
          (t i) +
        analyticOrderAt
          (fun w => ∏ j, g j w) (t i) at hord
    rw [hord, hcompOrder, hpairOrder, hsum,
      zero_add]
  · have hstarIm : (star (t i)).im ≠ 0 := by
      simp only [Complex.star_def, Complex.conj_im]
      exact neg_ne_zero.mpr (ne_of_gt (ht i))
    have hcompNe :
        movingCanonicalComplementProduct θ S
          (star (t i)) ≠ 0 :=
      movingCanonicalComplementProduct_ne_zero_of_im_ne_zero
        θ S hstarIm
    have hcompOrder :
        analyticOrderAt
            (movingCanonicalComplementProduct θ S)
            (star (t i)) = 0 :=
      (hcompAn (star (t i))).analyticOrderAt_eq_zero.mpr
        hcompNe
    have hgOrder : ∀ j, analyticOrderAt
        (g j) (star (t i)) =
          if j = i then 1 else 0 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp
        exact
          (movingCanonicalSurgeryPairFactor_zero_analyticOrderAt
            _ _ _ (ne_of_gt
              (movingCanonicalZero_pos θ (aIdx i)))
            (ne_of_gt
              (movingCanonicalZero_pos θ (bIdx i)))
            (htstar i)).2
      · rw [if_neg hji]
        apply (hgAn j
          (star (t i))).analyticOrderAt_eq_zero.mpr
        change
          movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx j))
            (movingCanonicalZero θ (bIdx j))
            (t j) (star (t i)) ≠ 0
        rw [Ne,
          movingCanonicalSurgeryPairFactor_eq_zero_iff
          _ _ _ _
          (ne_of_gt
            (movingCanonicalZero_pos θ (aIdx j)))
          (ne_of_gt
            (movingCanonicalZero_pos θ (bIdx j)))]
        rw [not_or]
        constructor
        · intro h
          have him := congrArg Complex.im h
          simp only [Complex.star_def,
            Complex.conj_im] at him
          linarith [ht i, ht j]
        · intro h
          apply hji
          exact (htinj (star_injective h)).symm
    have hpairOrder :=
      movingCanonicalSurgeryPairProduct_analyticOrderAt
        θ aIdx bIdx t (star (t i))
    have hsum : (∑ j, analyticOrderAt
        (g j) (star (t i))) = 1 := by
      simp_rw [hgOrder]
      simp
    have hpairAn : AnalyticAt ℂ
        (fun w => ∏ j, g j w) (star (t i)) := by
      have h := Finset.analyticAt_prod
        (𝕜 := ℂ) Finset.univ
        (fun j hj => hgAn j (star (t i)))
      have heq : (∏ j, g j) =
          fun w => ∏ j, g j w := by
        funext w
        rw [Finset.prod_apply]
      rwa [heq] at h
    have hord := analyticOrderAt_mul
      (hcompAn (star (t i))) hpairAn
    change analyticOrderAt
        (fun w =>
          movingCanonicalComplementProduct θ S w *
            ∏ j, g j w) (star (t i)) = 1
    change analyticOrderAt
        (fun w =>
          movingCanonicalComplementProduct θ S w *
            ∏ j, g j w) (star (t i)) =
      analyticOrderAt
          (movingCanonicalComplementProduct θ S)
          (star (t i)) +
        analyticOrderAt
          (fun w => ∏ j, g j w)
          (star (t i)) at hord
    rw [hord, hcompOrder, hpairOrder, hsum,
      zero_add]

theorem movingCanonicalSurgeryProduct_real_zero_analyticOrderAt
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (n : ℕ)
    (hn : n ∉
      movingCanonicalSurgerySelectedIndices
        aIdx bIdx) :
    analyticOrderAt
        (movingCanonicalSurgeryProduct
          θ aIdx bIdx t)
        (movingCanonicalZero θ n : ℂ) = 1 := by
  let S :=
    movingCanonicalSurgerySelectedIndices aIdx bIdx
  let r : ℂ := (movingCanonicalZero θ n : ℂ)
  let g : Fin k → ℂ → ℂ := fun j =>
    movingCanonicalSurgeryPairFactor
      (movingCanonicalZero θ (aIdx j))
      (movingCanonicalZero θ (bIdx j))
      (t j)
  have hcompAn : AnalyticAt ℂ
      (movingCanonicalComplementProduct θ S) r :=
    movingCanonicalComplementProduct_analytic θ S
      r (Set.mem_univ r)
  have hcompOrder :
      analyticOrderAt
          (movingCanonicalComplementProduct θ S) r = 1 :=
    movingCanonicalComplementProduct_zero_analyticOrderAt
      θ S n hn
  have hgAn : ∀ j, AnalyticAt ℂ (g j) r :=
    fun j =>
      movingCanonicalSurgeryPairFactor_analytic
        _ _ _ r (Set.mem_univ r)
  have hgNe : ∀ j, g j r ≠ 0 := by
    intro j
    change
      movingCanonicalSurgeryPairFactor
        (movingCanonicalZero θ (aIdx j))
        (movingCanonicalZero θ (bIdx j))
        (t j) r ≠ 0
    rw [Ne,
      movingCanonicalSurgeryPairFactor_eq_zero_iff
      _ _ _ _
      (ne_of_gt
        (movingCanonicalZero_pos θ (aIdx j)))
      (ne_of_gt
        (movingCanonicalZero_pos θ (bIdx j)))]
    rw [not_or]
    constructor
    · intro h
      have him := congrArg Complex.im h
      change (0 : ℝ) = (t j).im at him
      linarith [ht j]
    · intro h
      have him := congrArg Complex.im h
      simp only [Complex.star_def,
        Complex.conj_im] at him
      change (0 : ℝ) = -(t j).im at him
      linarith [ht j]
  have hpairAn : AnalyticAt ℂ
      (fun w => ∏ j, g j w) r := by
    have h := Finset.analyticAt_prod
      (𝕜 := ℂ) Finset.univ
      (fun j hj => hgAn j)
    have heq : (∏ j, g j) =
        fun w => ∏ j, g j w := by
      funext w
      rw [Finset.prod_apply]
    rwa [heq] at h
  have hpairNe : (∏ j, g j r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun j hj => hgNe j)
  have hpairOrder :
      analyticOrderAt
          (fun w => ∏ j, g j w) r = 0 :=
      hpairAn.analyticOrderAt_eq_zero.mpr hpairNe
  have hord := analyticOrderAt_mul hcompAn hpairAn
  change analyticOrderAt
      (fun w =>
        movingCanonicalComplementProduct θ S w *
          ∏ j, g j w) r = 1
  change analyticOrderAt
      (fun w =>
        movingCanonicalComplementProduct θ S w *
          ∏ j, g j w) r =
    analyticOrderAt
        (movingCanonicalComplementProduct θ S) r +
      analyticOrderAt
        (fun w => ∏ j, g j w) r at hord
  rw [hord, hcompOrder, hpairOrder, add_zero]

theorem movingCanonicalComplementProduct_orderOneEnvelope
    (θ : BoundedRealSequence) (S : Finset ℕ) :
    OrderOneEnvelope
      (movingCanonicalComplementProduct θ S) := by
  refine ⟨32, by norm_num, fun z => ?_⟩
  let u : ℕ → ℝ := fun n =>
    min
      (2 * ‖z‖ /
        ‖(movingCanonicalZero θ n : ℂ)‖)
      (2 * ‖z‖ ^ 2 /
        ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2)
  have hquad : Summable (fun n : ℕ =>
      2 * ‖z‖ ^ 2 /
        ‖(movingCanonicalZero θ n : ℂ)‖ ^ 2) := by
    refine
      (summable_movingCanonicalZero_inv_sq θ).mul_left
          (2 * ‖z‖ ^ 2) |>.congr
        (fun n => ?_)
    ring
  have hu : Summable u :=
    Summable.of_nonneg_of_le
      (fun n => le_min (by positivity) (by positivity))
      (fun n => min_le_right _ _) hquad
  have hsub :
      (∑' n : {n // n ∉ S}, u n.1) ≤
        ∑' n, u n :=
    Summable.tsum_subtype_le u
      {n : ℕ | n ∉ S}
      (fun n => le_min (by positivity) (by positivity))
      hu
  have hnorm :=
    RHTower.canonicalProductE1Indexed_norm_le_exp_min
      (fun n : {n // n ∉ S} =>
        (movingCanonicalZero θ n.1 : ℂ))
      (fun n => Complex.ofReal_ne_zero.mpr
        (ne_of_gt
          (movingCanonicalZero_pos θ n.1)))
      (RHTower.canonicalProductE1IndexedComplement_inv_sq_summable
        (fun n =>
          (movingCanonicalZero θ n : ℂ))
        (fun n => n ∈ S)
        (summable_movingCanonicalZero_inv_sq θ))
      z
  change ‖movingCanonicalComplementProduct θ S z‖ ≤ _
  calc
    ‖movingCanonicalComplementProduct θ S z‖ ≤
        Real.exp (∑' n : {n // n ∉ S}, u n.1) := by
      simpa [movingCanonicalComplementProduct,
        RHTower.canonicalProductE1IndexedComplement,
        u] using hnorm
    _ ≤ Real.exp (∑' n, u n) :=
      Real.exp_le_exp.mpr hsub
    _ ≤ Real.exp (orderOneWeight 32 z) :=
      Real.exp_le_exp.mpr
        (movingCanonicalGrowthSeries_le_orderOneWeight
          θ z)

theorem orderOneEnvelope_id :
    OrderOneEnvelope (fun z : ℂ => z) := by
  refine ⟨2, by norm_num, fun z => ?_⟩
  have hlog := Real.log_two_gt_d9
  have hweight :
      ‖z‖ ≤ orderOneWeight 2 z := by
    have hz := norm_nonneg z
    have hlogmono :
        Real.log 2 ≤ Real.log (2 + ‖z‖) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hbase :
        (1 + ‖z‖) * Real.log 2 ≤
          (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
      mul_le_mul_of_nonneg_left hlogmono (by linarith)
    have hcoef : (1 : ℝ) ≤ 2 * Real.log 2 := by
      nlinarith
    have hstep :
        1 + ‖z‖ ≤
          (2 * Real.log 2) * (1 + ‖z‖) :=
      by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hcoef
            (show 0 ≤ (1 + ‖z‖) by positivity))
    rw [orderOneWeight]
    calc
      ‖z‖ ≤ 1 + ‖z‖ := by linarith
      _ ≤ (2 * Real.log 2) * (1 + ‖z‖) := hstep
      _ = 2 * ((1 + ‖z‖) * Real.log 2) := by ring
      _ ≤ 2 * ((1 + ‖z‖) *
          Real.log (2 + ‖z‖)) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = 2 * (1 + ‖z‖) *
          Real.log (2 + ‖z‖) := by ring
  calc
    ‖z‖ ≤ orderOneWeight 2 z := hweight
    _ ≤ Real.exp (orderOneWeight 2 z) := by
      linarith
        [Real.add_one_le_exp
          (orderOneWeight 2 z)]

theorem orderOneEnvelope_linear_sub (t : ℂ) :
    OrderOneEnvelope (fun z : ℂ => z - t) := by
  have h := orderOneEnvelope_id.add
    (orderOneEnvelope_const (-t))
  exact h.congr (fun z => by ring)

theorem orderOneEnvelope_exp_linear (c : ℂ) :
    OrderOneEnvelope
      (fun z : ℂ => Complex.exp (c * z)) := by
  have hlog2 : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  let C : ℝ := 1 + ‖c‖ / Real.log 2
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun z => ?_⟩
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre :
      (c * z).re ≤ ‖c‖ * ‖z‖ := by
    exact (Complex.re_le_norm _).trans_eq
      (norm_mul c z)
  have hshape := log_two_le_shape z
  have hmain :
      ‖c‖ * ‖z‖ ≤ orderOneWeight C z := by
    have hz := norm_nonneg z
    have hc := norm_nonneg c
    have hlogmono :
        Real.log 2 ≤ Real.log (2 + ‖z‖) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hbase :
        (1 + ‖z‖) * Real.log 2 ≤
          (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
      mul_le_mul_of_nonneg_left hlogmono (by linarith)
    have hfrac : 0 ≤ ‖c‖ / Real.log 2 := by
      positivity
    have hshape0 :
        0 ≤ (1 + ‖z‖) *
          Real.log (2 + ‖z‖) :=
      shape_nonneg z
    rw [orderOneWeight]
    dsimp only [C]
    calc
      ‖c‖ * ‖z‖ ≤ ‖c‖ * (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
      _ = (‖c‖ / Real.log 2) *
          ((1 + ‖z‖) * Real.log 2) := by
        field_simp [hlog2.ne']
      _ ≤ (‖c‖ / Real.log 2) *
          ((1 + ‖z‖) *
            Real.log (2 + ‖z‖)) :=
        mul_le_mul_of_nonneg_left hbase hfrac
      _ ≤ (1 + ‖c‖ / Real.log 2) *
          ((1 + ‖z‖) *
            Real.log (2 + ‖z‖)) :=
        mul_le_mul_of_nonneg_right (by linarith) hshape0
      _ = (1 + ‖c‖ / Real.log 2) *
          (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
        ring
  exact hre.trans hmain

theorem OrderOneEnvelope.finsetProd
    {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, OrderOneEnvelope (f i)) :
    OrderOneEnvelope
      (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using orderOneEnvelope_const 1
  | @insert i s hi ih =>
      have hhead := hf i
        (Finset.mem_insert_self i s)
      have htail := ih
        (fun j hj =>
          hf j (Finset.mem_insert_of_mem hj))
      have hmul := hhead.mul htail
      exact hmul.congr (fun z => by
        rw [Finset.prod_insert hi])

theorem movingCanonicalSurgeryPairFactor_orderOneEnvelope
    (a b : ℝ) (t : ℂ) :
    OrderOneEnvelope
      (movingCanonicalSurgeryPairFactor a b t) := by
  let c : ℂ := (a : ℂ)⁻¹ + (b : ℂ)⁻¹
  let d : ℂ := ((a : ℂ) * (b : ℂ))⁻¹
  have h :=
    (((orderOneEnvelope_exp_linear c).const_mul d).mul
      (orderOneEnvelope_linear_sub t)).mul
        (orderOneEnvelope_linear_sub (star t))
  exact h.congr (fun z => by
    rw [movingCanonicalSurgeryPairFactor]
    dsimp only [c, d]
    have hexp :
        z / (a : ℂ) + z / (b : ℂ) =
          ((a : ℂ)⁻¹ + (b : ℂ)⁻¹) * z := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hexp, div_eq_mul_inv]
    ring)

theorem movingCanonicalSurgeryProduct_orderOneEnvelope
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    OrderOneEnvelope
      (movingCanonicalSurgeryProduct
        θ aIdx bIdx t) := by
  have hcomp :=
    movingCanonicalComplementProduct_orderOneEnvelope
      θ (movingCanonicalSurgerySelectedIndices
        aIdx bIdx)
  have hpairs :
      OrderOneEnvelope
        (fun z =>
          ∏ i, movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx i))
            (movingCanonicalZero θ (bIdx i))
            (t i) z) := by
    apply OrderOneEnvelope.finsetProd
    intro i hi
    exact
      movingCanonicalSurgeryPairFactor_orderOneEnvelope
        _ _ _
  exact (hcomp.mul hpairs).congr
    (fun z => by
      rw [movingCanonicalSurgeryProduct])

/-- Exponent-one convergence for a divisor indexed by an arbitrary type. -/
def HasExponentOfConvergenceOneIndexed
    {ι : Type*} (a : ι → ℂ) : Prop :=
  (∀ p : ℝ, 1 < p →
      Summable fun i => 1 / ‖a i‖ ^ p) ∧
    ¬Summable fun i => 1 / ‖a i‖

/-- Removing finitely many moving canonical zeros preserves exact exponent of convergence one. -/
theorem movingCanonicalComplementZero_hasExponentOfConvergenceOne
    (θ : BoundedRealSequence) (S : Finset ℕ) :
    HasExponentOfConvergenceOneIndexed
      (fun n : {n // n ∉ S} =>
        (movingCanonicalZero θ n.1 : ℂ)) := by
  constructor
  · intro p hp
    exact
      ((movingCanonicalZero_hasExponentOfConvergenceOne θ).1 p hp).subtype
        (fun n : ℕ => n ∉ S)
  · intro hcomp
    let f : ℕ → ℝ := fun n =>
      1 / ‖(movingCanonicalZero θ n : ℂ)‖
    have hindicator :
        Summable
          (({n : ℕ | n ∉ S} : Set ℕ).indicator f) :=
      summable_subtype_iff_indicator.mp hcomp
    have heq :
        ({n : ℕ | n ∉ S} : Set ℕ).indicator f
          =ᶠ[cofinite] f := by
      have hmem :
          {n : ℕ | n ∉ S} ∈ cofinite := by
        exact Set.Finite.compl_mem_cofinite S.finite_toSet
      filter_upwards [hmem] with n hn
      exact Set.indicator_of_mem hn f
    exact
      (movingCanonicalZero_hasExponentOfConvergenceOne θ).2
        (hindicator.congr_cofinite heq)

/-- Complete exact divisor-and-order package for the finite canonical-product surgery. -/
theorem movingCanonicalSurgeryProduct_exactOrderOneDivisor
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (htinj : Function.Injective t) :
    AnalyticOnNhd ℂ
        (movingCanonicalSurgeryProduct θ aIdx bIdx t)
        Set.univ ∧
      OrderOneEnvelope
        (movingCanonicalSurgeryProduct θ aIdx bIdx t) ∧
      HasExponentOfConvergenceOneIndexed
        (fun n :
            {n // n ∉
              movingCanonicalSurgerySelectedIndices
                aIdx bIdx} =>
          (movingCanonicalZero θ n.1 : ℂ)) ∧
      (∀ z,
        movingCanonicalSurgeryProduct
            θ aIdx bIdx t z = 0 ↔
          (∃ n : ℕ,
            n ∉
                movingCanonicalSurgerySelectedIndices
                  aIdx bIdx ∧
              z =
                (movingCanonicalZero θ n : ℂ)) ∨
            ∃ i : Fin k,
              z = t i ∨ z = star (t i)) ∧
      (∀ n,
        n ∉
            movingCanonicalSurgerySelectedIndices
              aIdx bIdx →
          analyticOrderAt
              (movingCanonicalSurgeryProduct
                θ aIdx bIdx t)
              (movingCanonicalZero θ n : ℂ) = 1) ∧
      ∀ i,
        analyticOrderAt
            (movingCanonicalSurgeryProduct
              θ aIdx bIdx t) (t i) = 1 ∧
          analyticOrderAt
            (movingCanonicalSurgeryProduct
              θ aIdx bIdx t) (star (t i)) = 1 := by
  exact
    ⟨movingCanonicalSurgeryProduct_analytic
        θ aIdx bIdx t,
      movingCanonicalSurgeryProduct_orderOneEnvelope
        θ aIdx bIdx t,
      movingCanonicalComplementZero_hasExponentOfConvergenceOne
        θ
          (movingCanonicalSurgerySelectedIndices
            aIdx bIdx),
      movingCanonicalSurgeryProduct_eq_zero_iff
        θ aIdx bIdx t,
      fun n hn =>
        movingCanonicalSurgeryProduct_real_zero_analyticOrderAt
          θ aIdx bIdx t ht n hn,
      fun i =>
        movingCanonicalSurgeryProduct_inserted_zero_analyticOrderAt
          θ aIdx bIdx t ht htinj i⟩

end

end GaloisForLFunctions.HTGeometry
