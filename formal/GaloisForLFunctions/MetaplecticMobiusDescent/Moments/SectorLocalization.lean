/-
Sector localization adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.FirstCoreRayAttachment

/-!
# Sector localization

Dyadic scales, annuli and retained and discarded weights of the centered-moment sector
localization; prime-power and CRT characters of the centered correlations.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
namespace CenteredMomentSectorLocalization
open CubicEisenstein  SchwartzPlanePoisson
local notation "O" => Eisenstein.O

def cutoff (x : ℝ) : ℝ := Real.smoothTransition (2-2*x)

theorem cutoff_one (x : ℝ) (hx : x ≤ 1/2) : cutoff x=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_zero (x : ℝ) (hx : 1 ≤ x) : cutoff x=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

def annulus (x : ℝ) : ℝ := cutoff x-cutoff (2*x)

theorem annulus_zero_low (x : ℝ) (hx : x ≤ 1/4) : annulus x=0 := by
  rw [annulus, cutoff_one x (by linarith),cutoff_one (2*x) (by linarith),sub_self]

theorem annulus_zero_high (x : ℝ) (hx : 1 ≤ x) : annulus x=0 := by
  rw [annulus,cutoff_zero x hx,cutoff_zero (2*x) (by linarith),sub_self]

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

theorem annulus_smooth : ContDiff ℝ ∞ annulus := by
  have hc : ContDiff ℝ ∞ cutoff :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact hc.sub (hc.comp (contDiff_const.mul contDiff_id))

def dyadicScale (n : ℤ) : ℝ := (2:ℝ)^n

theorem dyadicScale_pos (n : ℤ) : 0 < dyadicScale n := by
  unfold dyadicScale
  positivity

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

def dyadicWeight (n : ℤ) (q : ℝ) : ℝ := annulus (q/dyadicScale n)

theorem dyadicWeight_smooth (n : ℤ) : ContDiff ℝ ∞ (dyadicWeight n) :=
  annulus_smooth.comp (contDiff_id.div_const _)

theorem dyadicWeight_bounds (n : ℤ) (q : ℝ) :
    0 ≤ dyadicWeight n q ∧ dyadicWeight n q ≤ 1 := annulus_bounds _

theorem dyadicWeight_zero_low (n : ℤ) (q : ℝ) (hq : q ≤ dyadicScale n/4) :
    dyadicWeight n q=0 := by
  apply annulus_zero_low
  apply (div_le_iff₀ (dyadicScale_pos n)).mpr
  linarith

theorem dyadicWeight_zero_high (n : ℤ) (q : ℝ) (hq : dyadicScale n ≤ q) :
    dyadicWeight n q=0 := by
  apply annulus_zero_high
  exact (le_div_iff₀ (dyadicScale_pos n)).mpr (by simpa using hq)

theorem dyadicWeight_support (n : ℤ) :
    Function.support (dyadicWeight n) ⊆ Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  intro q hq
  constructor
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_low n q h))
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_high n q h))

theorem dyadicWeight_tsupport (n : ℤ) :
    tsupport (dyadicWeight n) ⊆ Set.Icc (dyadicScale n/4) (dyadicScale n) :=
  closure_minimal (fun _ h => Set.Ioo_subset_Icc_self (dyadicWeight_support n h)) isClosed_Icc

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_finite (q : ℝ) : (Function.support (fun n => dyadicWeight n q)).Finite := by
  by_cases hq : 0 < q
  · obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
    apply (Set.toFinite (({k+1,k+2} : Finset ℤ) : Set ℤ)).subset
    intro n hn
    by_contra hh
    exact hn (dyadicWeight_outside_pair q k hlo hhi n hh)
  · have hz : ∀ n,dyadicWeight n q=0 := fun n =>
      dyadicWeight_zero_low n q ((le_of_not_gt hq).trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))
    simp [hz]

theorem dyadicWeight_summable (q : ℝ) : Summable (fun n => dyadicWeight n q) :=
  summable_of_hasFiniteSupport (dyadicWeight_finite q)

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

def Retained (R : ℝ) (n : ℤ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q ≤ R ∧ q ∈ tsupport (dyadicWeight n)

def retainedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then dyadicWeight n q else 0

def discardedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then 0 else dyadicWeight n q

theorem retained_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then dyadicWeight n q else 0) :=
  (dyadicWeight_summable q).indicator {n | Retained R n}

theorem discarded_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then 0 else dyadicWeight n q) := by
  have h := (dyadicWeight_summable q).sub (retained_summable R q)
  apply h.congr
  intro n
  split_ifs <;> simp

theorem retained_add_discarded (R q : ℝ) (hq : 0 < q) :
    retainedWeight R q+discardedWeight R q=1 := by
  rw [retainedWeight,discardedWeight,← (retained_summable R q).tsum_add (discarded_summable R q)]
  convert dyadicWeight_partition q hq using 1
  apply tsum_congr
  intro n
  split_ifs <;> simp

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem retainedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : retainedWeight R q=0 := by
  simp [retainedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem discardedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : discardedWeight R q=0 := by
  simp [discardedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_nonneg (R q : ℝ) : 0 ≤ retainedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact (dyadicWeight_bounds n q).1
  · exact le_rfl

theorem discardedWeight_nonneg (R q : ℝ) : 0 ≤ discardedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact (dyadicWeight_bounds n q).1

theorem retainedWeight_bounds (R q : ℝ) : 0 ≤ retainedWeight R q ∧ retainedWeight R q ≤ 1 := by
  refine ⟨retainedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := discardedWeight_nonneg R q
    linarith
  · rw [retainedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem discardedWeight_bounds (R q : ℝ) : 0 ≤ discardedWeight R q ∧ discardedWeight R q ≤ 1 := by
  refine ⟨discardedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := retainedWeight_nonneg R q
    linarith
  · rw [discardedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem retained_scale_le (R : ℝ) (n : ℤ) (hn : Retained R n) : dyadicScale n ≤ 4*R := by
  obtain ⟨q,hq,hqR,hs⟩ := hn
  have hb := (dyadicWeight_tsupport n hs).1
  linarith

theorem retainedWeight_zero_above (R q : ℝ) (hq : 4*R ≤ q) : retainedWeight R q=0 := by
  unfold retainedWeight
  trans ∑' _n : ℤ, (0:ℝ)
  · apply tsum_congr
    intro n
    split_ifs with hn
    · exact dyadicWeight_zero_high n q ((retained_scale_le R n hn).trans hq)
    · rfl
  · exact tsum_zero

theorem retainedWeight_enclosure (R q : ℝ) (hq : retainedWeight R q ≠ 0) : 0 < q ∧ q ≤ 4*R := by
  constructor
  · exact lt_of_not_ge (fun h => hq (retainedWeight_zero_nonpos R q h))
  · exact le_of_not_gt (fun h => hq (retainedWeight_zero_above R q h.le))

theorem discardedWeight_zero_below (R q : ℝ) (hq : q ≤ R) : discardedWeight R q=0 := by
  by_cases hp : 0 < q
  · unfold discardedWeight
    trans ∑' _n : ℤ, (0:ℝ)
    · apply tsum_congr
      intro n
      split_ifs with hn
      · rfl
      · by_contra hne
        exact hn ⟨q,hp,hq,subset_tsupport _ hne⟩
    · exact tsum_zero
  · exact discardedWeight_zero_nonpos R q (le_of_not_gt hp)

theorem discardedWeight_support (R q : ℝ) (hq : discardedWeight R q ≠ 0) : R < q :=
  lt_of_not_ge (fun h => hq (discardedWeight_zero_below R q h))

theorem retainedWeight_one_below (R q : ℝ) (hq : 0 < q) (hR : q ≤ R) : retainedWeight R q=1 := by
  have h := retained_add_discarded R q hq
  rwa [discardedWeight_zero_below R q hR,add_zero] at h

theorem finite_retained_integral_dyads (R : ℝ) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, 1 ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc (1:ℤ) (k:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have : (2:ℝ)^(0:ℤ) < (2:ℝ)^n := by simpa [dyadicScale] using hq.trans_lt hs
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp this
    omega
  · have h : (2:ℝ)^n < (2:ℝ)^(k:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hk
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h
    omega

theorem annulus_pos (x : ℝ) (hlo : 1/4 < x) (hhi : x < 1) : 0 < annulus x := by
  by_cases hx : x ≤ 1/2
  · rw [annulus,cutoff_one x hx]
    have h := Real.smoothTransition.lt_one_of_lt_one (by linarith : 2-2*(2*x) < 1)
    exact sub_pos.mpr h
  · rw [annulus,cutoff_zero (2*x) (by linarith),sub_zero]
    exact Real.smoothTransition.pos_of_pos (by linarith)

theorem dyadicWeight_support_eq (n : ℤ) :
    Function.support (dyadicWeight n)=Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  apply Set.Subset.antisymm (dyadicWeight_support n)
  intro q hq
  apply ne_of_gt
  apply annulus_pos
  · apply (lt_div_iff₀ (dyadicScale_pos n)).mpr
    linarith [hq.1]
  · exact (div_lt_one (dyadicScale_pos n)).mpr hq.2

theorem dyadicWeight_tsupport_eq (n : ℤ) :
    tsupport (dyadicWeight n)=Set.Icc (dyadicScale n/4) (dyadicScale n) := by
  rw [tsupport,dyadicWeight_support_eq,closure_Ioo]
  linarith [dyadicScale_pos n]

theorem retained_iff_scale (R : ℝ) (n : ℤ) : Retained R n ↔ dyadicScale n ≤ 4*R := by
  refine ⟨retained_scale_le R n,fun hn => ?_⟩
  refine ⟨dyadicScale n/4,div_pos (dyadicScale_pos n) (by norm_num),by linarith,?_⟩
  rw [dyadicWeight_tsupport_eq]
  exact ⟨le_rfl,by linarith [dyadicScale_pos n]⟩

theorem retained_boundary (n : ℤ) : Retained (dyadicScale n/4) n := by
  rw [retained_iff_scale]
  linarith


end CenteredMomentSectorLocalization
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open InverseInitialRayAttachment InverseFirstRayAttachment TruncatedPrincipalPoisson
open scoped BigOperators Classical SchwartzMap ContDiff
open UniqueFactorizationMonoid
open Set
namespace CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

def indices (a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈Real.logb 2 a⌉ ⌊Real.logb 2 (4*b)⌋

lemma logb_dyadicScale (n : ℤ) : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

lemma mem_indices_iff_scale (a b : ℝ) (ha : 0< a) (hb : 0< b) (n : ℤ) :
    n∈indices a b ↔ a≤ dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

lemma mem_indices_iff_whole_support (a b : ℝ) (ha : 0< a) (hab : a≤ b) (n : ℤ) :
    n∈indices a b ↔ ∃q∈Icc a b,q∈tsupport (dyadicWeight n) := by
  rw [mem_indices_iff_scale a b ha (ha.trans_le hab) n]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨max a (dyadicScale n/4),⟨le_max_left _ _,max_le hab (by linarith)⟩,?_⟩
    rw [dyadicWeight_tsupport_eq]
    exact ⟨le_max_right _ _,max_le hlo (by linarith [dyadicScale_pos n])⟩
  · rintro ⟨q,hq,hq'⟩
    have hh := dyadicWeight_tsupport n hq'
    exact ⟨hq.1.trans hh.2,by linarith [hq.2,hh.1]⟩

lemma support_indices (a b q : ℝ) (ha : 0< a) (hq : q∈Icc a b)
    (n : ℤ) (hne : dyadicWeight n q≠0) : n∈indices a b :=
  (mem_indices_iff_whole_support a b ha (hq.1.trans hq.2) n).mpr
    ⟨q,hq,subset_tsupport _ hne⟩

lemma finite_active_indices (a b : ℝ) (ha : 0< a) (hab : a≤ b) :
    {n : ℤ | ∃q∈Icc a b,q∈tsupport (dyadicWeight n)}.Finite := by
  apply (indices a b).finite_toSet.subset
  intro n hn
  exact (mem_indices_iff_whole_support a b ha hab n).mpr hn

lemma logb_four_mul (b : ℝ) (hb : 0< b) :
    Real.logb 2 (4*b)=2+Real.logb 2 b := by
  rw [Real.logb_mul (by norm_num) hb.ne']
  congr 1
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem indices_card_bound (a b : ℝ) (ha : 0< a) (hab : a≤ b) :
    ((indices a b).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have hb := ha.trans_le hab
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha hab
  have hu := Int.ceil_lt_add_one (Real.logb 2 a)
  have hl := Int.sub_one_lt_floor (Real.logb 2 (4*b))
  have he := logb_four_mul b hb
  have hle : ⌈Real.logb 2 a⌉≤⌊Real.logb 2 (4*b)⌋+1 := by
    have hh : (⌈Real.logb 2 a⌉:ℝ)≤(⌊Real.logb 2 (4*b)⌋:ℝ)+1 := by linarith
    exact_mod_cast hh
  have hcard := Int.card_Icc_of_le _ _ hle
  have hcard' : ((indices a b).card:ℝ)=(⌊Real.logb 2 (4*b)⌋:ℝ)+1-(⌈Real.logb 2 a⌉:ℝ) := by
    exact_mod_cast hcard
  rw [hcard',Real.logb_div hb.ne' ha.ne']
  linarith [Int.floor_le (Real.logb 2 (4*b)),Int.le_ceil (Real.logb 2 a)]

theorem scaled_indices_card_bound (a b T : ℝ) (ha : 0< a) (hab : a≤ b) (hT : 0< T) :
    ((indices (a/T) (b/T)).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have h := indices_card_bound (a/T) (b/T) (div_pos ha hT)
    (div_le_div_of_nonneg_right hab hT.le)
  have he : (b/T)/(a/T)=b/a := by field_simp
  rwa [he] at h

lemma dyadic_partition_on_interval (a b q : ℝ) (ha : 0< a) (hq : q∈Icc a b) :
    (∑n∈indices a b,dyadicWeight n q)=1 := by
  rw [←dyadicWeight_partition q (ha.trans_le hq.1)]
  symm
  apply tsum_eq_sum
  intro n hn
  by_contra hne
  exact hn (support_indices a b q ha hq n hne)

theorem four_indices_card_bound (a b : Fin 4→ℝ)
    (ha : ∀j,0< a j) (hab : ∀j,a j≤ b j) :
    (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤
      ∏j:Fin 4,(3+Real.logb 2 (b j/a j)) := by
  rw [Fintype.card_pi]
  push_cast
  apply Finset.prod_le_prod
  · intro j hj
    positivity
  · intro j hj
    simpa only [Fintype.card_coe] using indices_card_bound (a j) (b j) (ha j) (hab j)

lemma retained_integral_mem (R q : ℝ) (hq : 1≤ q) (n : ℤ)
    (hr : Retained R n) (hne : dyadicWeight n q≠0) :
    n∈indices 1 (max 1 R) := by
  rw [mem_indices_iff_scale 1 (max 1 R) (by norm_num) (by positivity) n]
  exact ⟨hq.trans (dyadicWeight_support n hne).2.le,
    (retained_scale_le R n hr).trans (by linarith [le_max_right (1:ℝ) R])⟩

theorem indices_card_log_bound (C R Z a b : ℝ) (hC : 1≤ C) (hR : 0≤ R)
    (hZ : 1≤ Z) (ha : 0< a) (hab : a≤ b) (hratio : b/a≤ C*Z^R) :
    ((indices a b).card:ℝ)≤
      (3+Real.logb 2 C+R/Real.log 2)*(1+Real.log Z) := by
  have hb := ha.trans_le hab
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hCp : 0< C := zero_lt_one.trans_le hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (div_pos hb ha) hratio
  rw [Real.logb_mul hCp.ne' (Real.rpow_pos_of_pos hZp R).ne',
    Real.logb_rpow_eq_mul_logb_of_pos hZp] at hlog
  apply (indices_card_bound a b ha hab).trans
  have hc0 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
  have hz0 := Real.log_nonneg hZ
  have hr0 : 0≤ R/Real.log 2 := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hp := mul_nonneg (show 0≤3+Real.logb 2 C by linarith) hz0
  have he : R*Real.logb 2 Z=(R/Real.log 2)*Real.log Z := by unfold Real.logb;ring
  rw [he] at hlog
  nlinarith

theorem four_indices_subpower (C R ε : ℝ) (hC : 1≤ C) (hR : 0≤ R) (hε : 0<ε) :
    ∃D : ℝ,0< D ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ∀a b : Fin 4→ℝ,(∀j,0< a j) → (∀j,a j≤ b j) →
      (∀j,b j/a j≤ C*Z^R) →
      (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤ D*Z^ε := by
  let K : ℝ := 3+Real.logb 2 C+R/Real.log 2
  have hK : 0< K := by
    have hc := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
    have hr := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [K]
    linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨16*K^4,by positivity,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop (Real.exp 1),Filter.eventually_ge_atTop (1:ℝ)] with Z hlog hZexp hZ
  intro a b ha hab hratio
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hz : 1≤ Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hZexp
    simpa only [Real.log_exp] using hh
  have hp : (Real.log Z)^4≤ Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZp.le _),one_mul] using hlog
  have hcard : (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤(K*(1+Real.log Z))^4 := by
    rw [Fintype.card_pi]
    push_cast
    calc
      _ ≤ ∏j:Fin 4,K*(1+Real.log Z) := by
        apply Finset.prod_le_prod (by intros;positivity)
        intro j hj
        simpa only [Fintype.card_coe] using indices_card_log_bound C R Z (a j) (b j) hC hR hZ (ha j) (hab j) (hratio j)
      _ = _ := by simp
  calc
    _ ≤ (K*(1+Real.log Z))^4 := hcard
    _ ≤ (K*(2*Real.log Z))^4 := by gcongr;linarith
    _ = (16*K^4)*(Real.log Z)^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end CenteredMomentDyadicCount

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


open scoped BigOperators Classical
open NumberField
namespace CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
local instance : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)

def primePowerReduction (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    (𝓞 K ⧸ P ^ c) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.factor (by simpa using Ideal.pow_le_pow_right (I := P) hc)

omit [NumberField K] in
theorem primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _

def primePowerCharacter (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) : MulChar (𝓞 K ⧸ P ^ c) ℂ where
  __ := χ.toMonoidHom.comp (primePowerReduction P hc).toMonoidHom
  map_nonunit' := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change χ (Ideal.Quotient.mk P a) = 0
    apply χ.map_nonunit
    intro ha
    exact hx ((Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr ha)

omit [NumberField K] in
@[simp] theorem primePowerCharacter_apply (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) (x : 𝓞 K ⧸ P ^ c) :
    primePowerCharacter P hc χ x = χ (primePowerReduction P hc x) := rfl


end
end CenteredMomentCorrelation

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


open scoped BigOperators Classical
namespace CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

def crtCharacter {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) :
    MulChar S ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (e x) := fun h => hx ((isUnit_map_iff e x).mp h)
    have hsome : ∃ i, ¬IsUnit (e x i) := by
      by_contra h
      apply hn
      exact Pi.isUnit_iff.mpr (by simpa only [not_exists, not_not] using h)
    obtain ⟨i, hi⟩ := hsome
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((χ i).map_nonunit hi)

@[simp] theorem crtCharacter_apply {S ι : Type*} [CommRing S] [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] (e : S ≃+* (∀ i, R i)) (χ : ∀ i, MulChar (R i) ℂ) (x : S) :
    crtCharacter e χ x = ∏ i, χ i (e x i) := rfl

end
end CenteredMomentCorrelation

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
