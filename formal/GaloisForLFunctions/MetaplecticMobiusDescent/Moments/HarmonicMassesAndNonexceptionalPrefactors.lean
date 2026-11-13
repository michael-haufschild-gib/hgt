/-
Harmonic masses and nonexceptional prefactors adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.FirstAmplificationChoice

/-!
# Harmonic masses and nonexceptional prefactors

Common and radical harmonic mass weights, partition labels and common shells of the second
active count; input radius caps of the first dyadic count; scalar conductors of the first
nonexceptional prefactor.
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
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondActiveCount
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentRankinScale
open CenteredMomentRankinRadical
local notation "O" => Eisenstein.O

def commonShell (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) : Finset (Ideal O×Ideal O) :=
  (commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β))).filter
    (fun p=>(Ideal.absNorm (commonRadical p.1 p.2):ℝ)≤ Y)

def partitionLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Finset ((Ideal O×Ideal O)×Finset (Ideal O)) :=
  (commonShell S β Y).biUnion (fun p=>(primeSupport (commonRadical p.1 p.2)).powerset.image
    (fun U=>(p,U)))

theorem mem_partitionLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (p : (Ideal O×Ideal O)×Finset (Ideal O)) :
    p∈partitionLabels S β Y ↔ p.1∈commonShell S β Y ∧
      p.2⊆primeSupport (commonRadical p.1.1 p.1.2) := by
  simp only [partitionLabels,Finset.mem_biUnion,Finset.mem_image,Finset.mem_powerset]
  constructor
  · rintro ⟨q,hq,U,hU,rfl⟩
    exact ⟨hq,hU⟩
  · rintro ⟨hp,hU⟩
    exact ⟨p.1,hp,p.2,hU,rfl⟩

theorem active_common_data (S : Finset (Ideal O)) (β : Ideal O→ℂ) (s : Ideal O)
    (hs : Squarefree s) (hmask : ∀I∈S,β I≠0 → s∣I) (Y : ℝ)
    (p : Ideal O×Ideal O) (hp : p∈commonShell S β Y) :
    p.1≠0 ∧ p.2≠0 ∧ CubicEisenstein.primeSupport p.1=CubicEisenstein.primeSupport p.2 ∧
      s∣p.1 ∧ s∣p.2 := by
  have hm := (Finset.mem_filter.mp hp).1
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β p.1 p.2 hm
  have hsR := old_mask_dvd_commonRadical s I J hs hIs.1 hJs.1 (hmask I hi hβi) (hmask J hj hβj)
  refine ⟨hC ▸ commonPart_ne_zero I J,hD ▸ commonPart_ne_zero J I,?_,?_,?_⟩
  · rw [←hC,←hD]
    exact commonParts_equal_support I J
  · rw [←hC]
    exact hsR.trans (commonRadical_dvd_commonPart I J)
  · rw [←hD]
    have hr : commonRadical I J=commonRadical J I := by unfold commonRadical;rw [Finset.inter_comm]
    rw [hr] at hsR
    exact hsR.trans (commonRadical_dvd_commonPart J I)

theorem actual_partition_count (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃C:ℝ,0< C ∧ ∀Z p s₀:ℝ,1≤ Z → 0≤ p → p≤ B →
      ∀s:Ideal O,Squarefree s → s≠0 → Z^s₀≤(Ideal.absNorm s:ℝ) →
      ∀(S:Finset (Ideal O)) (β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → s∣I) →
      (∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ Z^B) →
      ((partitionLabels S β (Z^p)).card:ℝ)≤ C*Z^(p-s₀+δ) := by
  obtain ⟨C,hC,hcount⟩:=source_partition_count B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z p s₀ hZ hp hpB s hs hs0 hNs S β hmask hN
  have hd (v) (hv:v∈partitionLabels S β (Z^p)) :=
    active_common_data S β s hs hmask (Z^p) v.1 ((mem_partitionLabels S β (Z^p) v).mp hv).1
  apply hcount Z p s₀ hZ hp hpB s hs hs0 hNs _
  · intro v hv
    exact ⟨(hd v hv).1,(hd v hv).2.1⟩
  · intro v hv
    exact (hd v hv).2.2.1
  · intro v hv
    exact (hd v hv).2.2.2
  · intro v hv
    exact ((mem_partitionLabels S β (Z^p) v).mp hv).2
  · intro v hv
    exact commonLabel_norm_bounds S β (Z^B) hN v.1.1 v.1.2
      (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^p) v).mp hv).1).1
  · intro v hv
    exact (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^p) v).mp hv).1).2

end CenteredMomentSecondActiveCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentCommonHarmonicMass
open  UniqueFactorizationMonoid
open CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentDivisorAllocation CenteredMomentWholeDivisorShell
open CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => Eisenstein.O
abbrev Label := (Ideal O × Ideal O) × Finset (Ideal O)

def Valid (s : Ideal O) (v : Label) : Prop :=
  v.1.1 ≠ 0 ∧ v.1.2 ≠ 0 ∧ primeSupport v.1.1 = primeSupport v.1.2 ∧
  s ∣ v.1.1 ∧ s ∣ v.1.2 ∧ v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)

def weight (v : Label) : ℝ := 1 / Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm)

lemma commonRadical_norm_le (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    (Ideal.absNorm (commonRadical I J):ℝ) ≤ min (I.absNorm:ℝ) J.absNorm := by
  have hd : commonRadical I J ∣ I ∧ commonRadical I J ∣ J := by
    constructor <;> apply (squarefree_dvd_iff _ _ (commonRadical_squarefree I J)).mpr
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).1)
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).2)
  apply le_min
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm hd.1)
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
      (map_dvd Ideal.absNorm hd.2)

lemma min_le_sqrt_mul (x y : ℝ) (hx : 0≤ x) (hy : 0≤ y) :
    min x y ≤ Real.sqrt (x*y) := by
  apply (Real.le_sqrt (le_min hx hy) (mul_nonneg hx hy)).mpr
  rcases le_total x y with h|h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

lemma shell_scalar (e Y x y : ℝ) (he : 0< e) (hx : 0< x) (hy : 0< y)
    (hY : min x y ≤ Y) :
    (2*min x y)^(1+e)/Real.sqrt (x*y) ≤ 2^(1+e)*Y^e := by
  have hm : 0< min x y := lt_min hx hy
  have hsqrt : 0< Real.sqrt (x*y) := Real.sqrt_pos.2 (mul_pos hx hy)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hm.le,
    Real.rpow_add hm,Real.rpow_one]
  have hp := Real.rpow_le_rpow hm.le hY he.le
  have hs := min_le_sqrt_mul x y hx.le hy.le
  apply (div_le_iff₀ hsqrt).mpr
  calc
    _ ≤ 2^(1+e)*(Real.sqrt (x*y)*Y^e) := by gcongr
    _ = _ := by ring

theorem shell_bound (e : ℝ) (he : 0< e) :
    ∃C : ℝ,0< C ∧ ∀(s : Ideal O),Squarefree s → s≠0 →
      ∀(S : Finset Label),(∀v∈S,Valid s v) → ∀Y T₁ T₂ : ℝ,
      0< T₁ → 0< T₂ → min T₁ T₂≤ Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤ Y ∧ (v.1.2.absNorm:ℝ)≤ Y) →
      (∀v∈S,T₁≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*T₁ ∧
        T₂≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*T₂) →
      (∑v∈S,weight v)≤ C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro s hs hs0 S hS Y T₁ T₂ hT₁ hT₂ hTY hN hshell
  have hY : 0< Y := (lt_min hT₁ hT₂).trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hsq : 0< Real.sqrt (T₁*T₂) := Real.sqrt_pos.2 (mul_pos hT₁ hT₂)
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*min T₁ T₂) hY hY (by positivity) hN (by
      intro v hv
      apply (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
      exact min_le_min (hshell v hv).2.1.le (hshell v hv).2.2.2.le)
  calc
    _ ≤ ∑_v∈S,1/Real.sqrt (T₁*T₂) := by
      apply Finset.sum_le_sum
      intro v hv
      apply one_div_le_one_div_of_le hsq
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (hshell v hv).1 (hshell v hv).2.2.1 hT₂.le (hT₁.le.trans (hshell v hv).1)
    _ = (S.card:ℝ)/Real.sqrt (T₁*T₂) := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*min T₁ T₂)^(1+e)/(s.absNorm:ℝ))/Real.sqrt (T₁*T₂) :=
      div_le_div_of_nonneg_right hc hsq.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*min T₁ T₂)^(1+e)/Real.sqrt (T₁*T₂)) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (shell_scalar e Y T₁ T₂ he hT₁ hT₂ hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

def key (v : Label) : ℤ×ℤ := (normKey v.1.1,normKey v.1.2)
def keys (S : Finset Label) : Finset (ℤ×ℤ) := S.image key
def shell (S : Finset Label) (n : ℤ×ℤ) : Finset Label := S.filter (fun v=> key v=n)

lemma norm_scale_bounds (I : Ideal O) (hI : I≠0) (Y : ℝ) (hY : (I.absNorm:ℝ)≤ Y) :
    1≤ dyadicScale (normKey I) ∧ dyadicScale (normKey I)≤ Y := by
  have hn : 1≤(I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hk : 0≤ normKey I := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hn)
  refine ⟨?_,((normKey_eq_iff I hI _).mp rfl).1.trans hY⟩
  simpa only [dyadicScale,zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hk

lemma shell_norm_bounds (S : Finset Label) (n : ℤ×ℤ) (v : Label)
    (hv : v∈shell S n) (hC : v.1.1≠0) (hD : v.1.2≠0) :
    dyadicScale n.1≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*dyadicScale n.1 ∧
    dyadicScale n.2≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*dyadicScale n.2 := by
  have he := (Finset.mem_filter.mp hv).2
  have h₁ := (normKey_eq_iff v.1.1 hC n.1).mp (congrArg Prod.fst he)
  have h₂ := (normKey_eq_iff v.1.2 hD n.2).mp (congrArg Prod.snd he)
  exact ⟨h₁.1,h₁.2,h₂⟩

theorem sum_shells (S : Finset Label) (f : Label→ℝ) :
    (∑v∈S,f v)=∑n∈keys S,∑v∈shell S n,f v := by
  exact (Finset.sum_fiberwise_of_maps_to (fun v hv=> Finset.mem_image.mpr ⟨v,hv,rfl⟩) _).symm

lemma keys_card_log (B Z : ℝ) (hB : 0≤ B) (hZ : 1≤ Z) (S : Finset Label)
    (h0 : ∀v∈S,v.1.1≠0 ∧ v.1.2≠0)
    (hN : ∀v∈S,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) :
    ((keys S).card:ℝ)≤(3+B/Real.log 2)^2*(1+Real.log Z)^2 := by
  have hY : 1≤ Z^B := Real.one_le_rpow hZ hB
  have hsub : keys S ⊆ (indices 1 (Z^B))×ˢ(indices 1 (Z^B)) := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (h0 v hv).1 (Z^B) (hN v hv).1
    have hd := norm_scale_bounds v.1.2 (h0 v hv).2 (Z^B) (hN v hv).2
    apply Finset.mem_product.mpr
    constructor
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hc.1,hc.2.trans (by linarith)⟩
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hd.1,hd.2.trans (by linarith)⟩
  have hc : ((keys S).card:ℝ)≤((indices 1 (Z^B)).card:ℝ)^2 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product] at hh
    exact_mod_cast (by simpa only [pow_two] using hh)
  have hi := indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY (by simp)
  simp only [Real.logb_one,add_zero] at hi
  calc
    _ ≤ ((indices 1 (Z^B)).card:ℝ)^2 := hc
    _ ≤ ((3+B/Real.log 2)*(1+Real.log Z))^2 := by gcongr
    _ = _ := by ring

theorem polynomial_cap_log_bound (B e : ℝ) (hB : 0≤ B) (he : 0< e) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,1≤ Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (∑v∈S,weight v)≤ C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0< K := by dsimp [K]; positivity
  refine ⟨C*K^2,by positivity,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ×ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,weight v)≤ C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (hS v hv).1 (Z^B) (hN v hv).1
    have hm : min (dyadicScale n.1) (dyadicScale n.2)≤ Z^B := by
      have heq : normKey v.1.1=n.1 := congrArg Prod.fst hkey
      exact (min_le_left _ _).trans (heq ▸ hc.2)
    exact hbound s hs hs0 (shell S n) (fun w hw=> hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n.1) (dyadicScale n.2) (dyadicScale_pos _) (dyadicScale_pos _) hm
      (fun w hw=> hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=> shell_norm_bounds S n w hw (hS w (Finset.mem_filter.mp hw).1).1
        (hS w (Finset.mem_filter.mp hw).1).2.1)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K^2*(1+Real.log Z)^2)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K^2)*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

lemma log_square_subpower (d : ℝ) (hd : 0< d) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,1≤ Z → (1+Real.log Z)^2≤ C*Z^d := by
  let a : ℝ := d/2
  have ha : 0< a := by dsimp [a]; positivity
  refine ⟨(1+1/a)^2,by positivity,?_⟩
  intro Z hZ
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hp : 1≤ Z^a := Real.one_le_rpow hZ ha.le
  have hl := Real.log_le_rpow_div hz.le ha
  have hh : 1+Real.log Z≤(1+1/a)*Z^a := by
    calc
      _ ≤ Z^a+Z^a/a := add_le_add hp hl
      _ = _ := by ring
  calc
    _ ≤ ((1+1/a)*Z^a)^2 := by
      apply pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hh
    _ = (1+1/a)^2*Z^d := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le]
      congr 2
      dsimp [a]; ring

theorem common_harmonic_mass (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,2≤ Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (∑v∈S,1/Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm))≤ C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0< e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0< Z := by linarith
  have hZ1 : 1≤ Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := hbound Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr; exact hlog Z hZ1
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end CenteredMomentCommonHarmonicMass

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentOriginalCommonHarmonic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceZeroEnergy CenteredMomentAddedZeroUniform
open CenteredMomentSecondActiveCount CenteredMomentActiveSource CenteredMomentCommonHarmonicMass
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
 theorem actual_common_gates (s:Input ι) (R seed:Ideal O) (hs:Squarefree seed)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (C D:Ideal O)
    (hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))):
    C≠0 ∧ D≠0 ∧ CubicEisenstein.primeSupport C=CubicEisenstein.primeSupport D ∧
      seed∣C ∧ seed∣D ∧ (Ideal.absNorm C:ℝ)≤ sourceRadius s ∧ (Ideal.absNorm D:ℝ)≤ sourceRadius s:=by
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R seed
  have hm (I:Ideal O) (_:I∈S) (hI:β I≠0):seed∣I:=original_column_mask s R seed I hI
  have hp:(C,D)∈commonShell S β (Ideal.absNorm (CenteredMomentRankinRadical.commonRadical C D):ℝ):=
    Finset.mem_filter.mpr ⟨hlabel,le_rfl⟩
  have hh:=active_common_data S β seed hs hm _ (C,D) hp
  have hn:=commonLabel_norm_bounds S β (sourceRadius s)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2) C D hlabel
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hn⟩

omit [DecidableEq ι] in
 theorem actual_original_common_mass (B δ:ℝ) (hB:0≤ B) (hδ:0<δ):
    ∃C:ℝ,0< C ∧ ∀Z:ℝ,2≤ Z → ∀(s:Input ι),s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      ∀R seed:Ideal O,Squarefree seed → seed≠0 → ∀Y:ℝ,
      (∑v∈partitionLabels (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Y,
        1/Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm))≤ C*Z^δ/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hbound⟩:=common_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ s hz₁ hz₂ hcap R seed hs hs0 Y
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R seed
  have hm (I:Ideal O) (_:I∈S) (hI:β I≠0):seed∣I:=original_column_mask s R seed I hI
  have hN (I:Ideal O) (_:I∈S) (hI:β I≠0):(Ideal.absNorm I:ℝ)≤ Z^B:=
    (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hcap
  apply hbound Z hZ seed hs hs0 (partitionLabels S β Y)
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β Y v).mp hv
    have hh:=active_common_data S β seed hs hm Y v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    have hp:=(mem_partitionLabels S β Y v).mp hv
    exact commonLabel_norm_bounds S β (Z^B) hN v.1.1 v.1.2 (Finset.mem_filter.mp hp.1).1

end CenteredMomentOriginalCommonHarmonic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentDyadicCount

lemma indices_mono_upper (a b c : ℝ) (ha : 0< a) (hb : 0< b) (hbc : b≤ c) :
    indices a b ⊆ indices a c := by
  intro n hn
  rw [mem_indices_iff_scale a c ha (hb.trans_le hbc)]
  have h := (mem_indices_iff_scale a b ha hb n).mp hn
  exact ⟨h.1,h.2.trans (by linarith)⟩

lemma blocks_card_le (K R H nC nD : ℝ) (hH : 0< H)
    (hC : 1≤ nC) (hD : 1≤ nD) :
    Fintype.card (Blocks K R (H/nC) (H/nD)) ≤
      Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
        (![K,max 1 R,max 1 H,max 1 H] i))) := by
  have hcol (n : ℝ) (hn : 1≤ n) : indices 1 (H/n) ⊆ indices 1 (max 1 H) := by
    apply indices_mono_upper _ _ _ (by norm_num) (div_pos hH (zero_lt_one.trans_le hn))
    exact (div_le_self hH.le hn).trans (le_max_right _ _)
  have hs (i : Fin 4) : bands K R (H/nC) (H/nD) i ⊆
      indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i) := by
    fin_cases i
    · exact Finset.Subset.refl _
    · intro n hn
      obtain ⟨hr,q,hq,hne⟩ := (mem_retainedIndices R n).mp hn
      exact retained_integral_mem R q hq n hr hne
    · exact hcol nC hC
    · exact hcol nD hD
  let f : Blocks K R (H/nC) (H/nD) →
      (∀i:Fin 4,↥(indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i))) :=
    fun x i => ⟨x i,hs i (x i).property⟩
  apply Fintype.card_le_of_injective f
  intro x y hxy
  funext i
  apply Subtype.ext
  exact congrArg (fun z => (z i).val) hxy

theorem blocks_subpower (B L Cr ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (_hCr : 0< Cr) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀K R H nC nD : ℝ,0< K → 0< H → 1≤ nC → 1≤ nD →
      R≤ Cr*Z^L → H≤ Z^B →
      (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤ C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := four_indices_subpower (max 1 Cr) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro K R H nC nD hK hH hnC hnD hR hHcap
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hp : 1≤ Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hbound : 1≤ max 1 Cr*Z^(B+L) :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) hp
  have hR' : max 1 R≤ max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hR.trans (mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      (Real.rpow_nonneg hz.le _) (by positivity))
  have hH' : max 1 H≤ max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hHcap.trans ((Real.rpow_le_rpow_of_exponent_le hZ (by linarith : B≤ B+L)).trans
      (le_mul_of_one_le_left (zero_le_one.trans hp) (le_max_left _ _)))
  have hfour := hcount ![K,1,1,1] ![K,max 1 R,max 1 H,max 1 H]
    (by
      intro i
      fin_cases i
      · exact hK
      · exact zero_lt_one
      · exact zero_lt_one
      · exact zero_lt_one)
    (by
      intro i
      fin_cases i
      · exact le_rfl
      · exact le_max_left _ _
      · exact le_max_left _ _
      · exact le_max_left _ _)
    (by intro i;fin_cases i
        · change K / K ≤ _
          simpa only [div_self hK.ne'] using hbound
        · change max 1 R / 1 ≤ _
          simpa only [div_one] using hR'
        · change max 1 H / 1 ≤ _
          simpa only [div_one] using hH'
        · change max 1 H / 1 ≤ _
          simpa only [div_one] using hH')
  exact (show (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤
    Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
      (![K,max 1 R,max 1 H,max 1 H] i))) by
      exact_mod_cast blocks_card_le K R H nC nD hH hnC hnD).trans hfour

theorem original_blocks_subpower (B L Cr ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hCr : 0< Cr) (hε : 0<ε) :
    ∃C₀ : ℝ,0< C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D : Ideal Eisenstein.O), C≠0 → D≠0 →
      ∀(E : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
        (K R H : ℝ),0< K → 0< H → R≤ Cr*Z^L → H≤ Z^B →
      (Fintype.card (Blocks (effectiveScale C D E K) R
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤ C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩ := blocks_subpower B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hcount
  intro C D hC hD E K R H hK hH hR hHcap
  have norm_one (I : Ideal Eisenstein.O) (hI : I≠0) :
      (1:ℝ)≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hcount _ _ _ _ _ (effectiveScale_pos C D E K hK) hH
    (norm_one C hC) (norm_one D hD) hR hHcap

end CenteredMomentFirstPhysicalDyadicCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=> Eisenstein.O

lemma local_frequency_radius_cap (I J:Ideal O)(E:Finset (CommonIndex I J))
    (K V Z B ξ:ℝ)(hK:0< K)(hV:0≤ V)(hZ:1≤ Z)
    (hVcap:V≤ Z^B)(hKcap:K⁻¹≤ Z^B):
    frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K V) Z ξ≤ Z^(3*B+ξ/2) := by
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hT:V^2/K≤ Z^(3*B):=by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV hVcap 2) hKcap
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  unfold frequencyRadius
  calc
    _≤ Z^(3*B)*Z^(ξ/2):=mul_le_mul_of_nonneg_right
      ((first_nominal_scale_le I J E K V hK).trans hT) (Real.rpow_nonneg hz.le _)
    _=_:=by rw [←Real.rpow_add hz]

theorem original_local_blocks_subpower (B Hcap ξ ε:ℝ)
    (hB:0≤ B)(hHcap:0≤ Hcap)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0< C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K V H:ℝ),
      0< K→0≤ V→0< H→V≤ Z^B→K⁻¹≤ Z^B→H≤ Z^Hcap→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K V) Z ξ)
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤ C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_blocks_subpower Hcap (3*B+ξ/2) 1 ε
    hHcap (by positivity) (by norm_num) hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro C D hC hD E K V H hK hV hH hVcap hKcap hHbound
  exact hcount C D hC hD E K _ H hK hH
    (by simpa only [one_mul] using (local_frequency_radius_cap C D E K V Z B ξ
      hK hV hZ hVcap hKcap)) hHbound

open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair

lemma input_radius_cap {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B Z:ℝ)(s:Input ι)
    (hhi:∀i,|s.hi i|≤ hi i)(hb₁:|s.b₁|≤ b₁)(hb₂:|s.b₂|≤ b₂)
    (hZ:1≤ Z)(hfixed:(∏i,hi i)*b₁*b₂≤ Z)
    (hV:volume s.toData≤ Z^B):sourceRadius s≤ Z^(B+1) := by
  have hVol:0< volume s.toData:=volume_pos s.toData
  have he:sourceRadius s=(∏i,s.hi i)*s.b₁*s.b₂*volume s.toData:=by
    unfold sourceRadius CenteredMomentExceptionalAmplitudePair.volume;ring
  rw [he]
  have hprod:|∏i,s.hi i|≤∏i,hi i:=by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _=> abs_nonneg _) (fun i _=> hhi i)
  have hb₁0:0≤ b₁:=(abs_nonneg _).trans hb₁
  have hp0:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>(abs_nonneg _).trans (hhi i))
  have hbound:|(∏i,s.hi i)*s.b₁*s.b₂|≤(∏i,hi i)*b₁*b₂:=by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul hprod hb₁ (abs_nonneg _) hp0) hb₂
      (abs_nonneg _) (mul_nonneg hp0 hb₁0)
  have hcoeff:(∏i,s.hi i)*s.b₁*s.b₂≤ Z:=
    (le_abs_self _).trans (hbound.trans hfixed)
  calc
    _≤ Z*Z^B:=mul_le_mul hcoeff hV hVol.le (zero_le_one.trans hZ)
    _=Z^(B+1):=by rw [Real.rpow_add_one (ne_of_gt (zero_lt_one.trans_le hZ))];ring

theorem original_input_local_blocks_subpower {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)(hB:0≤ B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0< C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀s:Input ι,(∀i,|s.hi i|≤ hi i)→|s.b₁|≤ b₁→|s.b₂|≤ b₂→0< sourceRadius s→
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K:ℝ),
      0< K→volume s.toData≤ Z^B→K⁻¹≤ Z^B→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K (volume s.toData)) Z ξ)
        (sourceRadius s/Ideal.absNorm C) (sourceRadius s/Ideal.absNorm D)):ℝ)≤ C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩:=original_local_blocks_subpower B (B+1) ξ ε
    hB (by positivity) hξ hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ),
    Filter.eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hcount hZ hfixed
  intro s hhi hb₁ hb₂ hH C D hC hD E K hK hV hKi
  exact hcount C D hC hD E K _ _ hK (volume_pos s.toData).le hH hV hKi
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)

lemma input_radius_pos_of_live {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (hlive:coefficient s R seed I≠0):0< sourceRadius s := by
  obtain ⟨hI,hcap⟩:=original_column_norm s R seed I hz₁ hz₂ hlive
  exact (CenteredMomentFirstScale.norm_pos I hI).trans_le hcap

end CenteredMomentFirstPhysicalDyadicCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentSourceLowerSupport
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => Eisenstein.O

lemma tuple_norm_product {ι:Type*} [Fintype ι] (v:Tuple ι) :
    (Ideal.absNorm (finiteTupleProduct v):ℝ)=
      (∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ))*
      (Ideal.absNorm (v (Sum.inr 0)):ℝ)*(Ideal.absNorm (v (Sum.inr 1)):ℝ) := by
  simp only [finiteTupleProduct,map_prod,Nat.cast_prod,map_mul,Nat.cast_mul,Fintype.prod_sum_type,Fin.prod_univ_two]
  ring

 theorem profile_product_lower {ι:Type*} [Fintype ι]
    (R:Ideal O) (ν:ι→Ideal O→ℂ) (Wslot:ι→ℝ→ℂ) (P a:ι→ℝ)
    (W₁ W₂:ℝ→ℂ) (a₁ a₂ X₁ X₂ Y₁ Y₂ T:ℝ) (B₁ B₂ s:Ideal O)
    (hP:∀i,0< P i) (ha:∀i,0≤ a i) (ha₁:0≤ a₁) (ha₂:0≤ a₂)
    (hX₁:0< X₁) (hX₂:0< X₂) (hY₁:0< Y₁) (hY₂:0< Y₂)
    (hB₁:B₁≠0) (hB₂:B₂≠0) (hXT:X₁*X₂=T) (hYT:Y₁*Y₂=T)
    (hs:∀i x,Wslot i x≠0→a i≤ x)
    (hs₁:∀x,W₁ x≠0→a₁≤ x) (hs₂:∀x,W₂ x≠0→a₂≤ x)
    (v:Tuple ι) (hv:profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    (∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)≤
      (Ideal.absNorm (finiteTupleProduct v):ℝ) := by
  have hslot:∀i,Wslot i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/P i)≠0:=by
    intro i
    have hp: (∏j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))≠0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
    exact (mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ _))).2
  have hrect:idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))≠0:=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  have hslots:(∏i,a i)*(∏i,P i)≤∏i,(Ideal.absNorm (v (Sum.inl i)):ℝ):=by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun i _=> mul_nonneg (ha i) (hP i).le)
    intro i hi
    exact (le_div_iff₀ (hP i)).mp (hs i _ (hslot i))
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)< Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hplain:a₁*a₂*T≤(Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂*
      ((Ideal.absNorm (v (Sum.inr 0)):ℝ)*Ideal.absNorm (v (Sum.inr 1))) := by
    have hbranch (X Y:ℝ) (hX:0< X) (hY:0< Y) (hXY:X*Y=T)
        (hn:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X)*
          W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/Y)≠0) :
        a₁*a₂*T≤(Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂*
          ((Ideal.absNorm (v (Sum.inr 0)):ℝ)*Ideal.absNorm (v (Sum.inr 1))) := by
      have h1: a₁*X≤(Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ):=
        (le_div_iff₀ hX).mp (hs₁ _ (mul_ne_zero_iff.mp hn).1)
      have h2: a₂*Y≤(Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ):=
        (le_div_iff₀ hY).mp (hs₂ _ (mul_ne_zero_iff.mp hn).2)
      have hh:=mul_le_mul h1 h2 (mul_nonneg ha₂ hY.le) (Nat.cast_nonneg _)
      simp only [map_mul,Nat.cast_mul] at hh
      rw [←hXY]
      nlinarith
    unfold idealRectangle at hrect
    by_cases hx:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X₁)*
      W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/X₂)=0
    · have hy:W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/Y₁)*
        W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/Y₂)≠0:=by
        intro hy
        exact hrect (by rw [hx,hy,sub_self])
      exact hbranch Y₁ Y₂ hY₁ hY₂ hYT hy
    · exact hbranch X₁ X₂ hX₁ hX₂ hXT hx
  have hT:0< T:=hXT ▸ mul_pos hX₁ hX₂
  have hp:=mul_le_mul hslots hplain (mul_nonneg (mul_nonneg ha₁ ha₂) hT.le)
    (Finset.prod_nonneg (fun _ _=> Nat.cast_nonneg _))
  rw [tuple_norm_product]
  have he:(∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)=
      ((∏i,a i)*(∏i,P i)*(a₁*a₂*T))/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=by ring
  rw [he]
  apply (div_le_iff₀ (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))).mpr
  convert hp using 1 ; ring

 theorem profile_column_lower {ι:Type*} [Fintype ι]
    (R:Ideal O) (ν:ι→Ideal O→ℂ) (Wslot:ι→ℝ→ℂ) (P a:ι→ℝ)
    (W₁ W₂:ℝ→ℂ) (a₁ a₂ X₁ X₂ Y₁ Y₂ T:ℝ) (B₁ B₂ s:Ideal O)
    (hP:∀i,0< P i) (ha:∀i,0≤ a i) (ha₁:0≤ a₁) (ha₂:0≤ a₂)
    (hX₁:0< X₁) (hX₂:0< X₂) (hY₁:0< Y₁) (hY₂:0< Y₂)
    (hB₁:B₁≠0) (hB₂:B₂≠0) (hXT:X₁*X₂=T) (hYT:Y₁*Y₂=T)
    (hs:∀i x,Wslot i x≠0→a i≤ x)
    (hs₁:∀x,W₁ x≠0→a₁≤ x) (hs₂:∀x,W₂ x≠0→a₂≤ x)
    (S:Finset (Tuple ι)) (I:Ideal O)
    (hI:finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) :
    (∏i,a i)*a₁*a₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏i,P i)≤
      (Ideal.absNorm I:ℝ) := by
  obtain ⟨v,hv,hv0,he⟩:=CenteredMomentSupportedZeroEnergy.finiteColumnCoefficient_witness S
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I hI
  have hh:=profile_product_lower R ν Wslot P a W₁ W₂ a₁ a₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP ha ha₁ ha₂ hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hXT hYT hs hs₁ hs₂ v hv0
  simpa only [he] using hh

end CenteredMomentSourceLowerSupport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstPhysicalSource
open Eisenstein  
open CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentSupportedCorrelation
local notation "O"=> Eisenstein.O

theorem scalar_norm (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀:ℝ)(hK:0< K)(_hA₀:0< A₀)(_hB₀:0< B₀):
    ‖scalar C D hC E K A₀ B₀‖=
      ‖inactiveWeight C D E‖*K/
        (‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖*Real.sqrt A₀*Real.sqrt B₀):=by
  have he:0<‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖:=
    norm_pos_iff.mpr (ringComplex_ne_zero
      (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hk:0< K/‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos he)
  unfold scalar
  rw [norm_mul,norm_div,norm_mul,
    norm_canonicalNormalizedGauss (activePrime C D) (activeCoprime C D) (activeGood C D hC)
      (fun P=> common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=> netExponent_lt_six _ _)]
  simp only [mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hk,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end CenteredMomentFirstPhysicalSource

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstPhysicalSourceSupport
open Eisenstein  
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentFirstWholeKernel
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceLowerSupport CenteredMomentExceptionalAmplitudePair
local notation "O"=> Eisenstein.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem nonzero_columns (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    ∃a:columns C C hC.1 S,∃b:columns C D hD.1 S,
      c (C*(a:Ideal O))≠0 ∧ c (D*(b:Ideal O))≠0 ∧
      V 2 (Real.log (‖ringComplex (element C C hC.1 S a)‖^2/A₀))≠0 ∧
      V 3 (Real.log (‖ringComplex (element C D hD.1 S b)‖^2/B₀))≠0 := by
  unfold block at hn
  have hs:=right_ne_zero_of_mul hn
  obtain ⟨z,hz,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨a,ha,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  obtain ⟨b,hb,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hs
  dsimp only at hs
  split_ifs at hs with hab
  · have hprod:=left_ne_zero_of_mul (left_ne_zero_of_mul hs)
    have hc:=right_ne_zero_of_mul hprod
    have hw:=right_ne_zero_of_mul (left_ne_zero_of_mul hs)
    refine ⟨a,b,?_,?_,?_,?_⟩
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul hc)
    · have hh:=right_ne_zero_of_mul hc
      rw [star_ne_zero] at hh
      exact left_ne_zero_of_mul hh
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul hw)
    · exact right_ne_zero_of_mul hw
  · exact False.elim (hs rfl)

theorem original_column_lower {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed I:Ideal O)(a₁ a₂:ℝ)(ha₁:0≤ a₁)(ha₂:0≤ a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤ x)(hs₂:∀x,s.W₂ x≠0→a₂≤ x)
    (hn:CenteredMomentOriginalCommonHarmonic.coefficient s R seed I≠0):
    (∏i,s.lo i)*a₁*a₂*volume s.toData≤(I.absNorm:ℝ) := by
  have hh:=profile_column_lower R s.ν s.W s.P s.lo s.W₁ s.W₂ a₁ a₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos
    (fun i=>(s.lo_pos i).le) ha₁ ha₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product (fun i x hx=>(s.support i hx).1)
    hs₁ hs₂ (Fintype.piFinset s.pools) I (by
      simpa only [CenteredMomentOriginalCommonHarmonic.coefficient] using hn)
  simpa only [map_one,Nat.cast_one,mul_one,div_one,CenteredMomentExceptionalAmplitudePair.volume,mul_assoc] using hh

lemma log_window_upper (N H M:ℝ)(hN:0< N)(hH:0< H)
    (hlog:|Real.log (N/H)|≤ M):N≤ Real.exp M*H := by
  have hl:Real.log (N/H)≤ M:=(le_abs_self _).trans hlog
  have he:=Real.exp_le_exp.mpr hl
  rw [Real.exp_log (div_pos hN hH)] at he
  exact (div_le_iff₀ hH).mp he

theorem block_reference_lower (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀ a T M:ℝ)
    (hA:0< A₀)(hB:0< B₀)(hsource:∀I,c I≠0→a*T≤(I.absNorm:ℝ))
    (hwin:∀i y,V i y≠0→|y|≤ M)
    (hn:block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    a*T≤(C.absNorm:ℝ)*Real.exp M*A₀ ∧
      a*T≤(D.absNorm:ℝ)*Real.exp M*B₀ := by
  obtain ⟨i,j,hi,hj,hwi,hwj⟩:=nonzero_columns η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀ hn
  have hiN:(0:ℝ)<(i:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C C hC.1 S i).1)
  have hjN:(0:ℝ)<(j:Ideal O).absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C D hD.1 S j).1)
  have hni:‖ringComplex (element C C hC.1 S i)‖^2=((i:Ideal O).absNorm:ℝ):=by
    rw [ringComplex_norm_sq_eq_absNorm_span,element_span]
  have hnj:‖ringComplex (element C D hD.1 S j)‖^2=((j:Ideal O).absNorm:ℝ):=by
    rw [ringComplex_norm_sq_eq_absNorm_span,element_span]
  have hli:=hwin 2 _ hwi
  have hlj:=hwin 3 _ hwj
  rw [hni] at hli
  rw [hnj] at hlj
  have hsi:=hsource _ hi
  have hsj:=hsource _ hj
  simp only [map_mul,Nat.cast_mul] at hsi hsj
  constructor
  · exact hsi.trans (by nlinarith [log_window_upper _ _ M hiN hA hli])
  · exact hsj.trans (by nlinarith [log_window_upper _ _ M hjN hB hlj])

lemma reference_sqrt_lower (NC ND A₀ B₀ a T M:ℝ)
    (hNC:0≤ NC)(hND:0≤ ND)(hA:0≤ A₀)(_hB:0≤ B₀)(ha:0≤ a)(hT:0≤ T)
    (hl:a*T≤ NC*Real.exp M*A₀)(hr:a*T≤ ND*Real.exp M*B₀):
    a*T≤ Real.exp M*Real.sqrt (NC*ND)*(Real.sqrt A₀*Real.sqrt B₀) := by
  have hh:=mul_le_mul hl hr (mul_nonneg ha hT) (by positivity : 0≤ NC*Real.exp M*A₀)
  have hs:(a*T)^2≤(NC*ND)*(Real.exp M)^2*(A₀*B₀):=by nlinarith [hh]
  have hsqrt:=Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq (mul_nonneg ha hT),
    Real.sqrt_mul (mul_nonneg (mul_nonneg hNC hND) (sq_nonneg _)),
    Real.sqrt_mul (mul_nonneg hNC hND),Real.sqrt_sq (Real.exp_pos M).le,
    Real.sqrt_mul hA] at hsqrt
  nlinarith [hsqrt]

theorem scalar_volume_bound (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a T M:ℝ)(hK:0< K)(hA:0< A₀)(hB:0< B₀)(ha:0≤ a)(hT:0≤ T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*(a*T)≤
      Real.exp M*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖) := by
  have hs:=reference_sqrt_lower (C.absNorm:ℝ) (D.absNorm:ℝ) A₀ B₀ a T M
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA.le hB.le ha hT hl hr
  have hden:0< Real.sqrt A₀*Real.sqrt B₀:=mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hratio:(a*T)/(Real.sqrt A₀*Real.sqrt B₀)≤ Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm):=
    (div_le_iff₀ hden).mpr hs
  have hmu:‖inactiveWeight C D E‖≤1:=IdealCoprimeBilinearSieve.moebius_norm_le_one _
  rw [scalar_norm C D hC E K A₀ B₀ hK hA hB]
  calc
    _=(‖inactiveWeight C D E‖*K/
        (‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖))*((a*T)/(Real.sqrt A₀*Real.sqrt B₀)):=by ring
    _≤(‖inactiveWeight C D E‖*K/
        (‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖))*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)):=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _≤ _:=by
      have hh:=mul_le_mul_of_nonneg_right hmu (show 0≤ K/(‖ringComplex
        (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖)*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)) by positivity)
      convert hh using 1 <;> first | rfl | ring

theorem original_scalar_volume {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0< a₁)(ha₂:0< a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤ x)(hs₂:∀x,s.W₂ x≠0→a₂≤ x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀ M:ℝ)
    (hK:0< K)(hA:0< A₀)(hB:0< B₀)(hwin:∀i y,V i y≠0→|y|≤ M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0):
    ‖scalar C D hC E K A₀ B₀‖*volume s.toData≤
      (Real.exp M/((∏i,s.lo i)*a₁*a₂))*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖) := by
  let a:ℝ:=(∏i,s.lo i)*a₁*a₂
  have ha:0< a:=mul_pos (mul_pos (Finset.prod_pos (fun i _=> s.lo_pos i)) ha₁) ha₂
  have hV:0< volume s.toData:=volume_pos s.toData
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W V
    K K₀ H₀ A₀ B₀ a (volume s.toData) M hA hB
    (fun I hi=> original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  have hh:=scalar_volume_bound C D hC E K A₀ B₀ a (volume s.toData) M hK hA hB ha.le hV.le hl hr
  calc
    _=(‖scalar C D hC E K A₀ B₀‖*(a*volume s.toData))/a:=by field_simp
    _≤(Real.exp M*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖))/a:=div_le_div_of_nonneg_right hh ha.le
    _=_:=by dsimp only [a];ring

end CenteredMomentFirstPhysicalSourceSupport

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentCommonRadicalHarmonicMass
open  UniqueFactorizationMonoid
open CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentWholeDivisorShell CenteredMomentDyadicCount CenteredMomentSectorLocalization
open CenteredMomentCommonHarmonicMass (Label Valid commonRadical_norm_le norm_scale_bounds log_square_subpower)
local notation "O" => Eisenstein.O

def weight (v : Label) : ℝ := 1/(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)
def key (v : Label) : ℤ := normKey (commonRadical v.1.1 v.1.2)
def keys (S : Finset Label) : Finset ℤ := S.image key
def shell (S : Finset Label) (n : ℤ) : Finset Label := S.filter (fun v=> key v=n)

lemma radical_ne_zero (v : Label) : commonRadical v.1.1 v.1.2≠0 :=
  Squarefree.ne_zero (commonRadical_squarefree _ _)

lemma shell_scalar (e Y T : ℝ) (he : 0< e) (hT : 0< T) (hTY : T≤ Y) :
    (2*T)^(1+e)/T≤2^(1+e)*Y^e := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hT.le,
    Real.rpow_add hT,Real.rpow_one]
  calc
    _ = 2^(1+e)*T^e := by field_simp
    _ ≤ 2^(1+e)*Y^e := by gcongr

theorem shell_bound (e : ℝ) (he : 0< e) :
    ∃C : ℝ,0< C ∧ ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) → ∀Y T : ℝ,0< T → T≤ Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤ Y ∧ (v.1.2.absNorm:ℝ)≤ Y) →
      (∀v∈S,T≤(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ∧
        (Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)<2*T) →
      (∑v∈S,weight v)≤ C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro s hs hs0 S hS Y T hT hTY hN hshell
  have hY : 0< Y := hT.trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*T) hY hY (by positivity) hN
    (fun v hv=>(hshell v hv).2.le)
  calc
    _ ≤ ∑_v∈S,1/T := by
      apply Finset.sum_le_sum
      intro v hv
      exact one_div_le_one_div_of_le hT (hshell v hv).1
    _ = (S.card:ℝ)/T := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*T)^(1+e)/(s.absNorm:ℝ))/T :=
      div_le_div_of_nonneg_right hc hT.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*T)^(1+e)/T) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (shell_scalar e Y T he hT hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

lemma shell_norm_bounds (S : Finset Label) (n : ℤ) (v : Label) (hv : v∈shell S n) :
    dyadicScale n≤(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ∧
    (Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)<2*dyadicScale n := by
  exact (normKey_eq_iff _ (radical_ne_zero v) n).mp (Finset.mem_filter.mp hv).2

theorem sum_shells (S : Finset Label) (f : Label→ℝ) :
    (∑v∈S,f v)=∑n∈keys S,∑v∈shell S n,f v := by
  exact (Finset.sum_fiberwise_of_maps_to (fun v hv=> Finset.mem_image.mpr ⟨v,hv,rfl⟩) _).symm

lemma keys_card_log (B Z : ℝ) (hB : 0≤ B) (hZ : 1≤ Z) (S : Finset Label)
    (h0 : ∀v∈S,v.1.1≠0 ∧ v.1.2≠0)
    (hN : ∀v∈S,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) :
    ((keys S).card:ℝ)≤(3+B/Real.log 2)*(1+Real.log Z) := by
  have hY : 1≤ Z^B := Real.one_le_rpow hZ hB
  have hsub : keys S ⊆ indices 1 (Z^B) := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    have hr := (commonRadical_norm_le _ _ (h0 v hv).1 (h0 v hv).2).trans
      ((min_le_left _ _).trans (hN v hv).1)
    have hc := norm_scale_bounds _ (radical_ne_zero v) (Z^B) hr
    exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
      ⟨hc.1,hc.2.trans (by linarith)⟩
  have hc : ((keys S).card:ℝ)≤((indices 1 (Z^B)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hi := indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY (by simp)
  simp only [Real.logb_one,add_zero] at hi
  exact hc.trans hi

theorem polynomial_cap_log_bound (B e : ℝ) (hB : 0≤ B) (he : 0< e) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,1≤ Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (∑v∈S,weight v)≤ C*Z^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0< K := by dsimp [K]; positivity
  refine ⟨C*K,by positivity,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,weight v)≤ C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hr := (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      ((min_le_left _ _).trans (hN v hv).1)
    have hc := norm_scale_bounds _ (radical_ne_zero v) (Z^B) hr
    have hm : dyadicScale n≤ Z^B := by
      exact hkey ▸ hc.2
    exact hbound s hs hs0 (shell S n) (fun w hw=> hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n) (dyadicScale_pos _) hm
      (fun w hw=> hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=> shell_norm_bounds S n w hw)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K*(1+Real.log Z))*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K)*Z^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

theorem common_radical_harmonic_mass (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃C : ℝ,0< C ∧ ∀Z : ℝ,2≤ Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
      (∑v∈S,1/(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ))≤ C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0< e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0< Z := by linarith
  have hZ1 : 1≤ Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hl : 1+Real.log Z≤ D*Z^(δ/2) := by
    have hn := Real.log_nonneg hZ1
    exact (show 1+Real.log Z≤(1+Real.log Z)^2 by nlinarith).trans (hlog Z hZ1)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := hbound Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end CenteredMomentCommonRadicalHarmonicMass

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentSecondBlockCount
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondWholeKernel
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondBlockAggregate CenteredMomentSecondActiveCount
open CenteredMomentSecondSectorFrequency CenteredMomentSecondRetainedRows
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondSectorColumns CenteredMomentSecondRetainedAggregate
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentDyadicCount
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentActiveSource
local notation "O" => Eisenstein.O

lemma ideal_norm_ge_one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma sourceLower_le_upper (C D : Ideal O) (A : O) (K R H : ℝ) :
    ∀i,sourceLower C D A K i≤ sourceUpper C D A K R H i := by
  intro i
  fin_cases i
  · exact le_rfl
  all_goals exact le_max_left _ _

lemma source_ratio_bound (B L Cr Z : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (_hCr : 0< Cr) (hZ : 1≤ Z)
    (C D : Ideal O) (hC : C≠0) (hD : D≠0) (A : O) (hA : A≠0)
    (K R H : ℝ) (hK : 0< K) (hR : R≤ Cr*Z^L) (hH : H≤ Z^B) :
    ∀i,sourceUpper C D A K R H i/sourceLower C D A K i≤
      max 1 (4*Cr)*Z^(B+L) := by
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hp : 1≤ Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hc : 1≤ max 1 (4*Cr) := le_max_left _ _
  have hq : 1≤ max 1 (4*Cr)*Z^(B+L) := one_le_mul_of_one_le_of_one_le hc hp
  have hN := normValue_ge_one A hA
  have hNC := ideal_norm_ge_one C hC
  have hND := ideal_norm_ge_one D hD
  have hBpow : Z^B≤ Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hLpow : Z^L≤ Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hH' : H≤ max 1 (4*Cr)*Z^(B+L) :=
    hH.trans (hBpow.trans (le_mul_of_one_le_left (zero_le_one.trans hp) hc))
  have hR' : 4*R≤ max 1 (4*Cr)*Z^(B+L) := by
    calc
      _≤4*Cr*Z^L := by linarith
      _≤ max 1 (4*Cr)*Z^(B+L) :=
        mul_le_mul (le_max_right _ _) hLpow (Real.rpow_nonneg hz.le _) (by positivity)
  have hn (x d : ℝ) (hd : 1≤ d) (hx : x≤ max 1 (4*Cr)*Z^(B+L)) :
      max 1 (x/d)≤ max 1 (4*Cr)*Z^(B+L) := by
    apply max_le hq
    apply (div_le_iff₀ (zero_lt_one.trans_le hd)).mpr
    exact hx.trans (le_mul_of_one_le_right (by positivity) hd)
  intro i
  fin_cases i
  · simpa [sourceUpper,sourceLower,
      div_self (secondEffectiveScale_pos C D hC hD A hA K hK).ne'] using hq
  · simpa [sourceUpper,sourceLower] using hn (4*R) (normValue A) hN hR'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm C) hNC hH'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm D) hND hH'

theorem sourceBlocks_subpower (B L Cr ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hCr : 0< Cr) (hε : 0<ε) :
    ∃D₀:ℝ,0< D₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal O),Supported C → Supported D →
      ∀(U:Finset (CommonIndex C D))(K R H:ℝ),0< K →
      R≤ Cr*Z^L → H≤ Z^B →
      (Fintype.card (SourceBlocks C D U K R H):ℝ)≤ D₀*Z^ε := by
  obtain ⟨D₀,hD₀,hcount⟩ := four_indices_subpower (max 1 (4*Cr)) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨D₀,hD₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hc hZ
  intro C D hC hD U K R H hK hR hH
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  exact hc _ _ (sourceLower_pos C D hC.1 hD.1 _ hA K hK)
    (sourceLower_le_upper C D _ K R H)
    (source_ratio_bound B L Cr Z hB hL hCr hZ C D hC.1 hD.1 _ hA K R H hK hR hH)

abbrev CommonSubsets (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :=
  (p : commonShell S β Y) × Finset (CommonIndex p.val.1 p.val.2)

lemma commonSubset_support (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    U.image Subtype.val⊆primeSupport (commonRadical C D) := by
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
  rw [commonRadical_support]
  exact Q.property

def commonSubsetLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (q : CommonSubsets S β Y) : partitionLabels S β Y :=
  ⟨(q.1.val,q.2.image Subtype.val),
    (mem_partitionLabels S β Y _).mpr ⟨q.1.property,commonSubset_support _ _ q.2⟩⟩

lemma commonSubsetLabel_injective (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Function.Injective (commonSubsetLabel S β Y) := by
  rintro ⟨p,U⟩ ⟨q,V⟩ he
  have hp : p=q := Subtype.ext (congrArg (fun x=> x.val.1) he)
  cases hp
  have hU : U=V := Finset.image_injective Subtype.val_injective (congrArg (fun x=> x.val.2) he)
  cases hU
  rfl

lemma commonSubsets_card_le (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Fintype.card (CommonSubsets S β Y)≤(partitionLabels S β Y).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (commonSubsetLabel S β Y) (commonSubsetLabel_injective S β Y)

abbrev BlockLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y K R H : ℝ) :=
  (q : CommonSubsets S β Y) × SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H

lemma blockLabels_card_eq (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y K R H : ℝ) :
    (Fintype.card (BlockLabels S β Y K R H):ℝ)=
      ∑p : commonShell S β Y,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ) := by
  calc
    _ = ∑q : CommonSubsets S β Y,
        (Fintype.card (SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H):ℝ) := by
      exact_mod_cast Fintype.card_sigma (ι:=CommonSubsets S β Y)
        (α:=fun q=> SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H)
    _ = _ := Fintype.sum_sigma _

theorem actual_block_count (B L Cr ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hCr : 0< Cr) (hε : 0<ε) :
    ∃C₀:ℝ,0< C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀p s₀:ℝ,0≤ p → p≤ B →
      ∀s:Ideal O,Squarefree s → s≠0 → Z^s₀≤(Ideal.absNorm s:ℝ) →
      ∀(S:Finset (Ideal O)) (β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → s∣I) →
      ∀K R H:ℝ,0< K → R≤ Cr*Z^L → H≤ Z^B →
      (∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤ Z^B) →
      (Fintype.card (BlockLabels S β (Z^p) K R H):ℝ)≤ C₀*Z^(p-s₀+ε) := by
  obtain ⟨C₁,hC₁,hpart⟩ := actual_partition_count B (ε/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hblocks⟩ := sourceBlocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨C₁*C₂,by positivity,?_⟩
  filter_upwards [hblocks,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro p s₀ hp hpB s hs hs0 hNs S β hmask K R H hK hR hH hsource
  have hcount : (Fintype.card (CommonSubsets S β (Z^p)):ℝ)≤ C₁*Z^(p-s₀+ε/2) := by
    apply (Nat.cast_le.mpr (commonSubsets_card_le S β (Z^p))).trans
    exact hpart Z p s₀ hZ hp hpB s hs hs0 hNs S β hmask hsource
  have hbc (q : CommonSubsets S β (Z^p)) :
      (Fintype.card (SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H):ℝ)≤ C₂*Z^(ε/2) := by
    have hd := commonLabels_supported (activeSource S β) q.1.val.1 q.1.val.2
      (Finset.mem_filter.mp q.1.property).1
    exact hb _ _ hd.1 hd.2 q.2 K R H hK hR hH
  calc
    _ = ∑q : CommonSubsets S β (Z^p),
        (Fintype.card (SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H):ℝ) := by
      exact_mod_cast Fintype.card_sigma (ι:=CommonSubsets S β (Z^p))
        (α:=fun q=> SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H)
    _ ≤ ∑q : CommonSubsets S β (Z^p),C₂*Z^(ε/2) := Finset.sum_le_sum (fun q _=> hbc q)
    _ = (Fintype.card (CommonSubsets S β (Z^p)):ℝ)*(C₂*Z^(ε/2)) := by simp
    _ ≤ (C₁*Z^(p-s₀+ε/2))*(C₂*Z^(ε/2)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C₁*C₂)*Z^(p-s₀+ε) := by
      rw [mul_mul_mul_comm,←Real.rpow_add (zero_lt_one.trans_le hZ)]
      congr 2
      ring

end CenteredMomentSecondBlockCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentSecondBlockHarmonicMass
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate CenteredMomentSourceMass
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockCount
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentOriginalCommonHarmonic
local notation "O" => Eisenstein.O

abbrev ActiveSubsets (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  (p : ActiveLabel S β) × Finset (CommonIndex p.val.1 p.val.2)

abbrev ActiveBlocks (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :=
  (q : ActiveSubsets S β) × SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H

def pairWeight (C D : Ideal O) : ℝ := 1/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)

lemma pairWeight_nonneg (C D : Ideal O) : 0≤ pairWeight C D := by
  unfold pairWeight
  positivity

def activeSubsetLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (q : ActiveSubsets S β) : Label := (q.1.val,q.2.image Subtype.val)

lemma activeSubsetLabel_injective (S : Finset (Ideal O)) (β : Ideal O→ℂ) :
    Function.Injective (activeSubsetLabel S β) := by
  rintro ⟨p,U⟩ ⟨q,V⟩ he
  have hp : p=q := Subtype.ext (congrArg (fun x=> x.1) he)
  cases hp
  have hU : U=V := Finset.image_injective Subtype.val_injective
    (congrArg (fun x=> x.2) he)
  cases hU
  rfl

lemma active_common_shell (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤ Y) (p : ActiveLabel S β) :
    p.val∈commonShell S β Y := by
  have hs := commonLabels_supported (activeSource S β) _ _ p.property
  have hn := commonLabel_norm_bounds S β Y hN _ _ p.property
  exact Finset.mem_filter.mpr ⟨p.property,
    (commonRadical_norm_le _ _ hs.1.1 hs.2.1).trans ((min_le_left _ _).trans hn.1)⟩

lemma activeSubsetLabel_mem (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤ Y) (q : ActiveSubsets S β) :
    activeSubsetLabel S β q∈partitionLabels S β Y := by
  exact (mem_partitionLabels S β Y _).mpr
    ⟨active_common_shell S β Y hN q.1,commonSubset_support _ _ q.2⟩

lemma active_mass_le_partition (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤ Y) :
    (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
      pairWeight p.val.1 p.val.2)≤
    ∑v∈partitionLabels S β Y,pairWeight v.1.1 v.1.2 := by
  have he : (∑q : ActiveSubsets S β,pairWeight q.1.val.1 q.1.val.2)=
      ∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        pairWeight p.val.1 p.val.2 := Fintype.sum_sigma _
  rw [←he]
  let f := activeSubsetLabel S β
  calc
    _ = ∑v∈Finset.univ.image f,pairWeight v.1.1 v.1.2 := by
      rw [Finset.sum_image]
      · rfl
      · exact (activeSubsetLabel_injective S β).injOn
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro v hv;obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hv
          exact activeSubsetLabel_mem S β Y hN q)
      (fun v _ _=> pairWeight_nonneg _ _)

lemma active_blocks_sum_eq (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :
    (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)=
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ)*pairWeight p.val.1 p.val.2 := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Fintype.sum_sigma _

theorem actual_active_harmonic_mass (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃C:ℝ,0< C ∧ ∀Z:ℝ,2≤ Z → ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤ Z^B) →
      (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        pairWeight p.val.1 p.val.2)≤ C*Z^δ/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=common_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn
  apply (active_mass_le_partition S β (Z^B) hn).trans
  apply hb Z hZ seed hs hs0 (partitionLabels S β (Z^B))
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β (Z^B) v).mp hv
    have hh:=active_common_data S β seed hs hm (Z^B) v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    exact commonLabel_norm_bounds S β (Z^B) hn _ _
      (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^B) v).mp hv).1).1

theorem actual_block_harmonic_mass (B L Cr ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hCr : 0< Cr) (hε : 0<ε) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤ Z^B) →
      ∀K R H:ℝ,0< K → R≤ Cr*Z^L → H≤ Z^B →
      (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C₁,hC₁,hmass⟩:=actual_active_harmonic_mass B (ε/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hblocks⟩:=sourceBlocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  filter_upwards [hblocks,Filter.eventually_ge_atTop (2:ℝ)] with Z hb hZ
  intro seed hs hs0 S β hm hn K R H hK hR hH
  have hsum:=hmass Z hZ seed hs hs0 S β hm hn
  rw [active_blocks_sum_eq]
  calc
    _ ≤ ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (C₂*Z^(ε/2))*pairWeight p.val.1 p.val.2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      have hsupp:=commonLabels_supported (activeSource S β) _ _ p.property
      exact mul_le_mul_of_nonneg_right
        (hb _ _ hsupp.1 hsupp.2 U K R H hK hR hH) (pairWeight_nonneg _ _)
    _ = (C₂*Z^(ε/2))*(∑p : ActiveLabel S β,
        ∑U : Finset (CommonIndex p.val.1 p.val.2),pairWeight p.val.1 p.val.2) := by
      simp only [Finset.mul_sum]
    _ ≤ (C₂*Z^(ε/2))*(C₁*Z^(ε/2)/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (C₂*C₁)*Z^ε/(seed.absNorm:ℝ) := by
      calc
        _ = (C₂*C₁)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ) := by ring
        _ = _ := by rw [←Real.rpow_add (by linarith : 0< Z),add_halves]

theorem actual_original_block_harmonic_mass (B L Cr ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hCr : 0< Cr) (hε : 0<ε) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι] (s:CenteredMomentCommonRadialData.Input ι),
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      ∀puncture seed:Ideal O,Squarefree seed → seed≠0 →
      ∀K R H:ℝ,0< K → R≤ Cr*Z^L → H≤ Z^B →
      (∑q : ActiveBlocks (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s puncture seed) K R H,pairWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=actual_block_harmonic_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with Z hZ
  intro ι inst inst' s hz₁ hz₂ hcap puncture seed hs hs0 K R H hK hR hH
  exact hZ seed hs hs0 _ _
    (fun I _ hI=> original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap)
    K R H hK hR hH

end CenteredMomentSecondBlockHarmonicMass

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentSecondBlockRadicalHarmonicMass
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate CenteredMomentSourceMass
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockCount
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondBlockHarmonicMass (ActiveSubsets ActiveBlocks activeSubsetLabel activeSubsetLabel_injective activeSubsetLabel_mem)
local notation "O" => Eisenstein.O

def radicalWeight (C D:Ideal O):ℝ:=1/(Ideal.absNorm (commonRadical C D):ℝ)

lemma radicalWeight_nonneg (C D:Ideal O):0≤ radicalWeight C D:=by
  unfold radicalWeight
  positivity

lemma active_mass_le_partition (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤ Y) :
    (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
      radicalWeight p.val.1 p.val.2)≤
    ∑v∈partitionLabels S β Y,radicalWeight v.1.1 v.1.2 := by
  have he : (∑q : ActiveSubsets S β,radicalWeight q.1.val.1 q.1.val.2)=
      ∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        radicalWeight p.val.1 p.val.2 := Fintype.sum_sigma _
  rw [←he]
  let f := activeSubsetLabel S β
  calc
    _ = ∑v∈Finset.univ.image f,radicalWeight v.1.1 v.1.2 := by
      rw [Finset.sum_image]
      · rfl
      · exact (activeSubsetLabel_injective S β).injOn
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro v hv;obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hv
          exact activeSubsetLabel_mem S β Y hN q)
      (fun v _ _=> radicalWeight_nonneg _ _)

lemma active_blocks_sum_eq (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :
    (∑q : ActiveBlocks S β K R H,radicalWeight q.1.1.val.1 q.1.1.val.2)=
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ)*radicalWeight p.val.1 p.val.2 := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Fintype.sum_sigma _

theorem actual_active_radical_mass (B δ : ℝ) (hB : 0≤ B) (hδ : 0<δ) :
    ∃C:ℝ,0< C ∧ ∀Z:ℝ,2≤ Z → ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤ Z^B) →
      (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        radicalWeight p.val.1 p.val.2)≤ C*Z^δ/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=CenteredMomentCommonRadicalHarmonicMass.common_radical_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn
  apply (active_mass_le_partition S β (Z^B) hn).trans
  apply hb Z hZ seed hs hs0 (partitionLabels S β (Z^B))
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β (Z^B) v).mp hv
    have hh:=active_common_data S β seed hs hm (Z^B) v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    exact commonLabel_norm_bounds S β (Z^B) hn _ _
      (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^B) v).mp hv).1).1

theorem actual_block_radical_mass (B L Cr ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hCr : 0< Cr) (hε : 0<ε) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤ Z^B) →
      ∀K R H:ℝ,0< K → R≤ Cr*Z^L → H≤ Z^B →
      (∑q : ActiveBlocks S β K R H,radicalWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C₁,hC₁,hmass⟩:=actual_active_radical_mass B (ε/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hblocks⟩:=sourceBlocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  filter_upwards [hblocks,Filter.eventually_ge_atTop (2:ℝ)] with Z hb hZ
  intro seed hs hs0 S β hm hn K R H hK hR hH
  have hsum:=hmass Z hZ seed hs hs0 S β hm hn
  rw [active_blocks_sum_eq]
  calc
    _ ≤ ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (C₂*Z^(ε/2))*radicalWeight p.val.1 p.val.2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      have hsupp:=commonLabels_supported (activeSource S β) _ _ p.property
      exact mul_le_mul_of_nonneg_right
        (hb _ _ hsupp.1 hsupp.2 U K R H hK hR hH) (radicalWeight_nonneg _ _)
    _ = (C₂*Z^(ε/2))*(∑p : ActiveLabel S β,
        ∑U : Finset (CommonIndex p.val.1 p.val.2),radicalWeight p.val.1 p.val.2) := by
      simp only [Finset.mul_sum]
    _ ≤ (C₂*Z^(ε/2))*(C₁*Z^(ε/2)/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (C₂*C₁)*Z^ε/(seed.absNorm:ℝ) := by
      calc
        _ = (C₂*C₁)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ) := by ring
        _ = _ := by rw [←Real.rpow_add (by linarith : 0< Z),add_halves]

theorem actual_original_block_radical_mass (B L Cr ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hCr : 0< Cr) (hε : 0<ε) :
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι] (s:CenteredMomentCommonRadialData.Input ι),
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      ∀puncture seed:Ideal O,Squarefree seed → seed≠0 →
      ∀K R H:ℝ,0< K → R≤ Cr*Z^L → H≤ Z^B →
      (∑q : ActiveBlocks (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s puncture seed) K R H,radicalWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=actual_block_radical_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with Z hZ
  intro ι inst inst' s hz₁ hz₂ hcap puncture seed hs hs0 K R H hK hR hH
  exact hZ seed hs hs0 _ _
    (fun I _ hI=> original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap)
    K R H hK hR hH

end CenteredMomentSecondBlockRadicalHarmonicMass

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstInactiveRadicalMass
open Eisenstein CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonRadialData CenteredMomentRankinRadical
open CenteredMomentSecondBlockAggregate CenteredMomentSupportedCorrelation
local notation "O"=> Eisenstein.O

def inactiveWeight (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ):ℝ:=
  ‖(UniqueFactorizationMonoid.moebius (∏P∈E,P.val):ℂ)‖/
    ((Ideal.absNorm (∏P∈E,P.val):ℝ)^a)

lemma inactiveWeight_nonneg (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ):
    0 ≤ inactiveWeight C D E a:=by
  unfold inactiveWeight
  exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma inactiveWeight_le_one (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ)(ha:0≤ a):
    inactiveWeight C D E a≤1:=by
  have hE:(∏P∈E,P.val)≠(0:Ideal O):=by
    have he:=TruncatedPrincipalPoisson.primeSubsetGenerator_ne_zero (fun P:CommonIndex C D=> P.val) E
    have hh:=Ideal.span_singleton_eq_bot.not.mpr he
    simpa only [TruncatedPrincipalPoisson.primeSubsetGenerator_span,
      Ideal.zero_eq_bot] using hh
  have hn:1≤(Ideal.absNorm (∏P∈E,P.val):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hp:1≤(Ideal.absNorm (∏P∈E,P.val):ℝ)^a:=Real.one_le_rpow hn ha
  unfold inactiveWeight
  exact (div_le_self (norm_nonneg _) hp).trans (IdealCoprimeBilinearSieve.moebius_norm_le_one _)

theorem actual_inactive_radical_mass (B ε:ℝ)(hB:0≤ B)(hε:0<ε):
    ∃C:ℝ,0< C ∧ ∀Z:ℝ,2≤ Z→∀seed:Ideal O,Squarefree seed→seed≠0→
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0→seed∣I)→(∀I∈S,β I≠0→(I.absNorm:ℝ)≤ Z^B)→
      ∀a:ℝ,0≤ a→
      (∑p:ActiveLabel S β,∑E∈inactiveSubsets p.val.1 p.val.2,
        inactiveWeight p.val.1 p.val.2 E a/
          (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ))≤ C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_active_radical_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn a ha
  apply le_trans _ (hb Z hZ seed hs hs0 S β hm hn)
  apply Finset.sum_le_sum
  intro p hp
  calc
    _≤∑_E∈inactiveSubsets p.val.1 p.val.2,radicalWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro E hE
      exact div_le_div_of_nonneg_right (inactiveWeight_le_one _ _ E a ha) (Nat.cast_nonneg _)
    _≤∑_E:Finset (CommonIndex p.val.1 p.val.2),radicalWeight p.val.1 p.val.2:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _=> radicalWeight_nonneg _ _)

theorem original_input_inactive_radical_mass (B ε:ℝ)(hB:0≤ B)(hε:0<ε):
    ∃C:ℝ,0< C ∧ ∀Z:ℝ,2≤ Z→∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι),
      s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤ Z^B→
      ∀puncture seed:Ideal O,Squarefree seed→seed≠0→∀a:ℝ,0≤ a→
      (∑p:ActiveLabel (finiteColumns (Fintype.piFinset s.pools)) (coefficient s puncture seed),
        ∑E∈inactiveSubsets p.val.1 p.val.2,
          inactiveWeight p.val.1 p.val.2 E a/
            (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ))≤ C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_inactive_radical_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ ι _ _ s hz₁ hz₂ hcap puncture seed hs hs0 a ha
  exact hb Z hZ seed hs hs0 _ _
    (fun I _ hI=> original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap) a ha

end CenteredMomentFirstInactiveRadicalMass

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentFirstActiveRadicalBudget
open Eisenstein CanonicalQuadraticSieve CompletedGauss 
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentRankinRadical CenteredMomentFirstInactiveRadicalMass
open CenteredMomentSupportedCorrelation
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
local notation "O"=> Eisenstein.O

lemma active_exponent_budget (i j:ℕ)(hi:0 < i)(hj:0 < j):
    2+(if netExponent i j≠0 then 1 else 0) ≤ i+j:=by
  unfold netExponent
  split_ifs <;> omega

theorem radical_squared_active_dvd (I J:Ideal O):
    commonRadical I J^2*Ideal.span {activeConductor I J}∣commonPart I J*commonPart J I:=by
  have hr:commonRadical I J=∏P:CommonIndex I J,P.val:=by
    exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P=> P)).symm
  have ha:Ideal.span {activeConductor I J}=
      ∏P:CommonIndex I J,if netExponent (leftExponent I J P) (rightExponent I J P)≠0 then P.val else 1:=by
    rw [activeConductor,span_finitePrimeModulus]
    change (∏P:ActiveIndex I J,P.val.val)=_
    rw [Finset.prod_coe_sort]
    simp only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.prod_filter]
  rw [hr,ha,←Finset.prod_pow,←Finset.prod_mul_distrib,
    commonPart_left_product,commonPart_right_product,←Finset.prod_mul_distrib]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  have hh:=active_exponent_budget (leftExponent I J P) (rightExponent I J P)
    (leftExponent_pos I J P) (rightExponent_pos I J P)
  rw [←pow_add]
  convert pow_dvd_pow P.val hh using 1
  split_ifs <;> simp [pow_succ]

theorem radical_active_norm (I J:Ideal O)(hI:I≠0)(hJ:J≠0):
    (Ideal.absNorm (commonRadical I J):ℝ)^2*
      (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤(I.absNorm:ℝ)*J.absNorm:=by
  have hd:commonRadical I J^2*Ideal.span {activeConductor I J}∣I*J:=
    (radical_squared_active_dvd I J).trans (mul_dvd_mul (commonPart_dvd I J hI) (commonPart_dvd J I hJ))
  have hn:=Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hI hJ)))
    (map_dvd Ideal.absNorm hd)
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using (show
    (Ideal.absNorm (commonRadical I J^2*Ideal.span {activeConductor I J}):ℝ)≤
      (Ideal.absNorm (I*J):ℝ) by exact_mod_cast hn)

theorem active_root_le_radical (I J:Ideal O)(hI:I≠0)(hJ:J≠0):
    Real.sqrt (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)/
      Real.sqrt ((I.absNorm:ℝ)*J.absNorm)≤1/(Ideal.absNorm (commonRadical I J):ℝ):=by
  have hR:0<(Ideal.absNorm (commonRadical I J):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero I J))
  have hN:0<(I.absNorm:ℝ)*J.absNorm:=mul_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
  have hh:=Real.sqrt_le_sqrt (radical_active_norm I J hI hJ)
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hR.le] at hh
  exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hN) hR).mpr (by simpa [mul_comm] using hh)

theorem actual_first_weighted_mass (B ε:ℝ)(hB:0≤ B)(hε:0<ε):
    ∃C:ℝ,0< C ∧ ∀Z:ℝ,2≤ Z→∀seed:Ideal O,Squarefree seed→seed≠0→
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0→seed∣I)→(∀I∈S,β I≠0→(I.absNorm:ℝ)≤ Z^B)→
      ∀a:ℝ,0≤ a→
      (∑p:ActiveLabel S β,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        inactiveWeight p.val.1 p.val.2 E a*
          (Real.sqrt (Ideal.absNorm (Ideal.span {activeConductor p.val.1 p.val.2}):ℝ)/
            Real.sqrt ((p.val.1.absNorm:ℝ)*p.val.2.absNorm)))≤ C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_inactive_radical_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn a ha
  apply le_trans _ (hb Z hZ seed hs hs0 S β hm hn a ha)
  apply Finset.sum_le_sum
  intro p hp
  have hsupp:=commonLabels_supported (activeSource S β) _ _ p.property
  apply Finset.sum_le_sum
  intro E hE
  exact (mul_le_mul_of_nonneg_left (active_root_le_radical _ _ hsupp.1.1 hsupp.2.1)
    (inactiveWeight_nonneg _ _ E a)).trans_eq (by ring)

theorem original_first_weighted_mass (B ε:ℝ)(hB:0≤ B)(hε:0<ε):
    ∃C:ℝ,0< C ∧ ∀Z:ℝ,2≤ Z→∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι),
      s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤ Z^B→
      ∀puncture seed:Ideal O,Squarefree seed→seed≠0→∀a:ℝ,0≤ a→
      (∑p:ActiveLabel (finiteColumns (Fintype.piFinset s.pools)) (coefficient s puncture seed),
        ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
          inactiveWeight p.val.1 p.val.2 E a*
            (Real.sqrt (Ideal.absNorm (Ideal.span {activeConductor p.val.1 p.val.2}):ℝ)/
              Real.sqrt ((p.val.1.absNorm:ℝ)*p.val.2.absNorm)))≤ C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_first_weighted_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ ι _ _ s hz₁ hz₂ hcap puncture seed hs hs0 a ha
  exact hb Z hZ seed hs hs0 _ _
    (fun I _ hI=> original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap) a ha

end CenteredMomentFirstActiveRadicalBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentFirstNonexceptionalPrefactor
open Eisenstein   HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalSourceSupport
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstActiveRadicalBudget CenteredMomentRankinRadical
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentSupportedCorrelation
local notation "O"=> Eisenstein.O

lemma pair_conductor_root (q₁ q₂ B:ℝ)(_h₁:0≤ q₁)(h₂:0≤ q₂)
    (hB:0≤ B)(hb₁:q₁≤ B)(hb₂:q₂≤ B):Real.sqrt (q₁*q₂)≤ B := by
  have hh:=mul_le_mul hb₁ hb₂ h₂ hB
  have hs:=Real.sqrt_le_sqrt hh
  simpa only [←pow_two,Real.sqrt_sq hB] using hs

lemma scalar_conductor_algebra (s μ K T N E r C F q q₁ q₂:ℝ)
    (_hs:0≤ s)(hμ:0≤μ)(hK:0≤ K)(_hT:0< T)(hN:0< N)(hE:0< E)(hr:0< r)
    (hC:0≤ C)(hF:0≤ F)(hq:0≤ q)(h₁:0≤ q₁)(h₂:0≤ q₂)
    (hscalar:s*T≤μ*C*K*Real.sqrt N/(E*r))
    (hc₁:q₁≤ F*q*E*r^2)(hc₂:q₂≤ F*q*E*r^2):
    s*T/N*Real.sqrt (q₁*q₂)≤μ*C*F*K*q*(r/Real.sqrt N) := by
  have hroot:=pair_conductor_root q₁ q₂ (F*q*E*r^2) h₁ h₂ (by positivity) hc₁ hc₂
  calc
    _≤(μ*C*K*Real.sqrt N/(E*r))/N*(F*q*E*r^2):=
      mul_le_mul (div_le_div_of_nonneg_right hscalar hN.le) hroot
        (Real.sqrt_nonneg _) (by positivity)
    _=μ*C*F*K*q*(r/Real.sqrt N):=by
      have hn:Real.sqrt N≠0:=ne_of_gt (Real.sqrt_pos.mpr hN)
      have hn2:=Real.sq_sqrt hN.le
      field_simp
      linear_combination μ*C*K*F*q*hn2

theorem weighted_scalar_volume (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀ a T M:ℝ)(hK:0< K)(hA:0< A₀)(hB:0< B₀)(ha:0< a)(hT:0< T)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖*T≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*K*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/
        (‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖) := by
  have hs:=reference_sqrt_lower (C.absNorm:ℝ) (D.absNorm:ℝ) A₀ B₀ a T M
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hA.le hB.le ha.le hT.le hl hr
  have hden:0< Real.sqrt A₀*Real.sqrt B₀:=mul_pos (Real.sqrt_pos.2 hA) (Real.sqrt_pos.2 hB)
  have hratio:T/(Real.sqrt A₀*Real.sqrt B₀)≤ Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a:=by
    apply (div_le_div_iff₀ hden ha).mpr
    nlinarith [hs]
  rw [scalar_norm C D hC E K A₀ B₀ hK hA hB]
  calc
    _=(‖inactiveWeight C D E‖*K/
        (‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖))*(T/(Real.sqrt A₀*Real.sqrt B₀)):=by ring
    _≤(‖inactiveWeight C D E‖*K/
        (‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
          ‖ringComplex (activeConductor C D)‖))*(Real.exp M*Real.sqrt ((C.absNorm:ℝ)*D.absNorm)/a):=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _=_:=by ring

theorem actual_scalar_conductors (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (E:Finset (CommonIndex C D))(η τ₁ τ₂:Character)
    (K A₀ B₀ a T M F:ℝ)(hK:0< K)(hA:0< A₀)(hB:0< B₀)(ha:0< a)(hT:0< T)(hF:0≤ F)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤ F*(η.modulus.absNorm:ℝ)*
      ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
      ‖ringComplex (activeConductor C D)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤ F*(η.modulus.absNorm:ℝ)*
      ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
      ‖ringComplex (activeConductor C D)‖^2):
    ‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*F*K*(η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm := by
  have hN:0<(C.absNorm:ℝ)*D.absNorm:=mul_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1))
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1))
  have he:0<‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖:=
    norm_pos_iff.mpr (ringComplex_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hrpos:0<‖ringComplex (activeConductor C D)‖:=
    norm_pos_iff.mpr (ringComplex_ne_zero (supported_element_ne_zero _ (activeConductor_supported C D hC)))
  have hh:=scalar_conductor_algebra _ _ K T _ _ _ (Real.exp M/a) F (η.modulus.absNorm:ℝ)
    (τ₁.modulus.absNorm:ℝ) (τ₂.modulus.absNorm:ℝ) (norm_nonneg _) (norm_nonneg _)
    hK.le hT hN (sq_pos_of_pos he) hrpos (by positivity) hF (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (weighted_scalar_volume C D hC E K A₀ B₀ a T M hK hA hB ha hT hl hr) hc₁ hc₂
  have hroot:=active_root_le_radical C D hC.1 hD.1
  rw [←ringComplex_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)] at hroot
  exact hh.trans ((mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by ring))

theorem original_scalar_conductors {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0< a₁)(ha₂:0< a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤ x)(hs₂:∀x,s.W₂ x≠0→a₂≤ x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M F:ℝ)(τ₁ τ₂:Character)
    (hK:0< K)(hA:0< A₀)(hB:0< B₀)(hF:0≤ F)(hwin:∀i y,V i y≠0→|y|≤ M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0)
    (hc₁:(τ₁.modulus.absNorm:ℝ)≤ F*(s.η.modulus.absNorm:ℝ)*
      ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
      ‖ringComplex (activeConductor C D)‖^2)
    (hc₂:(τ₂.modulus.absNorm:ℝ)≤ F*(s.η.modulus.absNorm:ℝ)*
      ‖ringComplex (TruncatedPrincipalPoisson.primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E)‖^2*
      ‖ringComplex (activeConductor C D)‖^2):
    ‖scalar C D hC E K A₀ B₀‖*volume s.toData/((C.absNorm:ℝ)*D.absNorm)*
      Real.sqrt ((τ₁.modulus.absNorm:ℝ)*τ₂.modulus.absNorm)≤
      ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*F*K*(s.η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm := by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=> s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C D hC hD E rows W V
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (volume s.toData) M hA hB
    (fun I hi=> original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_scalar_conductors C D hC hD E s.η τ₁ τ₂ K A₀ B₀ _ _ M F hK hA hB
    ha (volume_pos s.toData) hF hl hr hc₁ hc₂

end CenteredMomentFirstNonexceptionalPrefactor

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
