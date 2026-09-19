import GaloisForLFunctions.RHTower.MobiusDivisorTwoDebtSourceCycle
import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedWindowRepair
import GaloisForLFunctions.HTGeometry.InwardPlaneDisplacementReturn

/-!
# Actual prime batches producing positive inherited covariance

The source profiles at child cutoffs `2`, `11`, and `15` admit an affine
lower bound for `2*x*y` with a positive constant term. This bound persists
under small independent clipping. Fresh inward selection keeps the vector
sum bounded, so the affine bound produces covariance proportional to the
number of distinct actual primes, with one bounded boundary loss.

`eventually_exists_mobiusDivisorPositiveDebtBatches` supplies the parent
windows and prepared core unconditionally. Every prefix has bounded signed
displacement, a common quadratic successor-energy ceiling, and a linear
reduction of the complete external prime-two cost.

`eventually_exists_mobiusDivisorJointDebtNeutralization` starts selection at
minus the actual receiving pair. One batch of square-root length neutralizes
that pair, releases its initial squared energy plus `M`, and removes at least
`M * sqrt M` from the complete inherited cost. Every raw-energy prefix has
only a linear allowance. The covariance surplus also pays the square reserve.

This is a finite source producer. Its quantifiers do not assert sufficient
capacity to pay arbitrary quadratic debt or an exhaustive prime order.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower
open HTGeometry

/-- Interpolating covariance at the three actual profiles gives a positive intercept. -/
private lemma debt_affine_plane :
    ∃ a b g : ℝ, 0 < g ∧ ∀ K ∈ ({2,11,15}:Finset ℕ),
      g+a*(mobiusDivisorNormalizedTwoProfile K).1+b*(mobiusDivisorNormalizedTwoProfile K).2 =
        2*(mobiusDivisorNormalizedTwoProfile K).1*(mobiusDivisorNormalizedTwoProfile K).2 := by
  obtain ⟨hA,hzero,hxz,hz,hy,hw⟩ := mobiusDivisorNormalizedTwoProfile_debt_signs
  let A := (mobiusDivisorNormalizedTwoProfile 2).1
  let x := (mobiusDivisorNormalizedTwoProfile 11).1
  let y := (mobiusDivisorNormalizedTwoProfile 11).2
  let z := (mobiusDivisorNormalizedTwoProfile 15).1
  let w := (mobiusDivisorNormalizedTwoProfile 15).2
  change 0 < A at hA
  change x < z at hxz
  change z < 0 at hz
  change y < 0 at hy
  change 0 < w at hw
  let D := (x-A)*w-(z-A)*y
  have hD : D < 0 := by
    have h1 := mul_neg_of_neg_of_pos (show x-A < 0 by linarith) hw
    have h2 := mul_pos_of_neg_of_neg (show z-A < 0 by linarith) hy
    dsimp [D]
    linarith only [h1,h2]
  let a := 2*y*w*(x-z)/D
  let b := (2*x*y-a*(x-A))/y
  let g := -a*A
  have ha : a < 0 := div_neg_of_pos_of_neg
    (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith : 2*y < 0) hw)
      (sub_neg.mpr hxz)) hD
  refine ⟨a,b,g,mul_pos (neg_pos.mpr ha) hA,?_⟩
  intro K hK
  simp only [mem_insert,mem_singleton] at hK
  rcases hK with rfl|rfl|rfl
  · rw [hzero]
    change g+a*A+b*0=2*A*0
    dsimp [g]
    ring
  · change g+a*x+b*y=2*x*y
    dsimp [g,b]
    field_simp [hy.ne]
    ring
  · change g+a*z+b*w=2*z*w
    have had : a*((x-A)*w-(z-A)*y)=2*y*w*(x-z) := div_mul_cancel₀ _ hD.ne
    have hby : b*y=2*x*y-a*(x-A) := div_mul_cancel₀ _ hy.ne
    have he : (g+a*z+b*w-2*z*w)*y=0 := by
      dsimp only [g]
      linear_combination w*hby-had
    have hh := (mul_eq_zero.mp he).resolve_right hy.ne
    linarith only [hh]

private lemma debt_uniform_margin :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ × ℝ,
      c*‖z‖ ≤ max
        (z.1*(mobiusDivisorNormalizedTwoProfile 2).1+z.2*(mobiusDivisorNormalizedTwoProfile 2).2)
        (max (z.1*(mobiusDivisorNormalizedTwoProfile 11).1+z.2*(mobiusDivisorNormalizedTwoProfile 11).2)
          (z.1*(mobiusDivisorNormalizedTwoProfile 15).1+z.2*(mobiusDivisorNormalizedTwoProfile 15).2)) := by
  apply exists_threePlaneSource_margin
  intro z hz0
  obtain ⟨hA,hzero,hxz,hx,hy,hw⟩ := mobiusDivisorNormalizedTwoProfile_debt_signs
  have hxy : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hz0 (Prod.ext hn.1 hn.2)
  by_cases hz : 0 < z.1
  · apply lt_of_lt_of_le _ (le_max_left _ _)
    rw [hzero,mul_zero,add_zero]
    exact mul_pos hz hA
  have hz1 : z.1 ≤ 0 := le_of_not_gt hz
  by_cases hz2 : z.2 < 0
  · apply lt_of_lt_of_le _ ((le_max_left _ _).trans (le_max_right _ _))
    exact add_pos_of_nonneg_of_pos (mul_nonneg_of_nonpos_of_nonpos hz1 (hxz.trans hx).le)
      (mul_pos_of_neg_of_neg hz2 hy)
  · apply lt_of_lt_of_le _ ((le_max_right _ _).trans (le_max_right _ _))
    have hz2' : 0 ≤ z.2 := le_of_not_gt hz2
    by_cases hz1' : z.1=0
    · have hz2p : 0 < z.2 := lt_of_le_of_ne hz2'
        (by rcases hxy with h|h; exact False.elim (h hz1'); exact Ne.symm h)
      rw [hz1',zero_mul,zero_add]
      exact mul_pos hz2p hw
    · exact add_pos_of_pos_of_nonneg (mul_pos_of_neg_of_neg (lt_of_le_of_ne hz1 hz1') hx)
        (mul_nonneg hz2' hw.le)

private lemma debt_clip_continuous (K : ℕ) (hK : 0 < K) :
    ContinuousAt (mobiusDivisorNormalizedTwoClip K) 0 := by
  have hd : ContinuousAt (fun u : ℝ => Real.sqrt K+u*(Real.sqrt (K+1:ℕ)-Real.sqrt K)) 0 := by fun_prop
  have hn : Real.sqrt K+(0:ℝ)*(Real.sqrt (K+1:ℕ)-Real.sqrt K) ≠ 0 := by
    simpa using (Real.sqrt_pos.mpr (show 0 < (K:ℝ) by exact_mod_cast hK)).ne'
  have h0 : ContinuousAt (fun u : ℝ => (mobiusDivisorCoupledTwoInterpolatedProfile K u).1) 0 := by
    dsimp [mobiusDivisorCoupledTwoInterpolatedProfile]; fun_prop
  have h1 : ContinuousAt (fun u : ℝ => (mobiusDivisorCoupledTwoInterpolatedProfile K u).2) 0 := by
    dsimp [mobiusDivisorCoupledTwoInterpolatedProfile]; fun_prop
  exact (h0.div hd hn).prodMk (h1.div hd hn)

private lemma debt_clip_zero (K : ℕ) :
    mobiusDivisorNormalizedTwoClip K 0=mobiusDivisorNormalizedTwoProfile K := by
  simp [mobiusDivisorNormalizedTwoClip,mobiusDivisorCoupledTwoInterpolatedProfile,
    mobiusDivisorNormalizedTwoProfile]

private lemma debt_clip_geometry :
    ∃ ε c B g a b : ℝ, 0 < ε ∧ 0 < c ∧ 0 < B ∧ 0 < g ∧
      (∀ K ∈ ({2,11,15}:Finset ℕ), ∀ u : ℝ, |u| ≤ ε →
        ‖mobiusDivisorNormalizedTwoClip K u‖ ≤ B ∧
        g+a*(mobiusDivisorNormalizedTwoClip K u).1+b*(mobiusDivisorNormalizedTwoClip K u).2 ≤
          2*(mobiusDivisorNormalizedTwoClip K u).1*(mobiusDivisorNormalizedTwoClip K u).2) ∧
      ∀ u v w : ℝ, |u| ≤ ε → |v| ≤ ε → |w| ≤ ε → ∀ z : ℝ × ℝ,
        c*‖z‖ ≤ max
          (z.1*(mobiusDivisorNormalizedTwoClip 2 u).1+z.2*(mobiusDivisorNormalizedTwoClip 2 u).2)
          (max (z.1*(mobiusDivisorNormalizedTwoClip 11 v).1+z.2*(mobiusDivisorNormalizedTwoClip 11 v).2)
            (z.1*(mobiusDivisorNormalizedTwoClip 15 w).1+z.2*(mobiusDivisorNormalizedTwoClip 15 w).2)) := by
  obtain ⟨a,b,g,hg,haff⟩ := debt_affine_plane
  obtain ⟨c,hc,hmargin⟩ := debt_uniform_margin
  let B : ℝ := 1+‖mobiusDivisorNormalizedTwoProfile 2‖+
    ‖mobiusDivisorNormalizedTwoProfile 11‖+‖mobiusDivisorNormalizedTwoProfile 15‖
  have hB : 0 < B := by dsimp [B]; positivity
  have hBbase : ∀ K ∈ ({2,11,15}:Finset ℕ), ‖mobiusDivisorNormalizedTwoProfile K‖ < B := by
    intro K hK
    simp only [mem_insert,mem_singleton] at hK
    rcases hK with rfl|rfl|rfl <;> dsimp [B] <;>
      linarith [norm_nonneg (mobiusDivisorNormalizedTwoProfile 2),
        norm_nonneg (mobiusDivisorNormalizedTwoProfile 11),norm_nonneg (mobiusDivisorNormalizedTwoProfile 15)]
  have hall : ∀ᶠ u : ℝ in nhds 0, ∀ K ∈ ({2,11,15}:Finset ℕ),
      ‖mobiusDivisorNormalizedTwoClip K u‖ < B ∧
      g/2 < 2*(mobiusDivisorNormalizedTwoClip K u).1*(mobiusDivisorNormalizedTwoClip K u).2-
        a*(mobiusDivisorNormalizedTwoClip K u).1-b*(mobiusDivisorNormalizedTwoClip K u).2 ∧
      ‖mobiusDivisorNormalizedTwoClip K u-mobiusDivisorNormalizedTwoProfile K‖ < c/4 := by
    rw [eventually_all_finset]
    intro K hK
    have hKpos : 0 < K := by
      simp only [mem_insert,mem_singleton] at hK
      rcases hK with rfl|rfl|rfl <;> omega
    have hcont := debt_clip_continuous K hKpos
    have hcontq : ContinuousAt (fun u =>
        2*(mobiusDivisorNormalizedTwoClip K u).1*(mobiusDivisorNormalizedTwoClip K u).2-
          a*(mobiusDivisorNormalizedTwoClip K u).1-b*(mobiusDivisorNormalizedTwoClip K u).2) 0 := by
      exact (((hcont.fst.const_mul 2).mul hcont.snd).sub
        (hcont.fst.const_mul a)).sub (hcont.snd.const_mul b)
    have hq : g/2 < 2*(mobiusDivisorNormalizedTwoClip K 0).1*(mobiusDivisorNormalizedTwoClip K 0).2-
        a*(mobiusDivisorNormalizedTwoClip K 0).1-b*(mobiusDivisorNormalizedTwoClip K 0).2 := by
      rw [debt_clip_zero]
      linarith only [haff K hK,hg]
    have hcnear : ContinuousAt (fun u =>
        ‖mobiusDivisorNormalizedTwoClip K u-mobiusDivisorNormalizedTwoProfile K‖) 0 :=
      (hcont.sub continuousAt_const).norm
    exact (hcont.norm.eventually (eventually_lt_nhds (by simpa [debt_clip_zero] using hBbase K hK))).and
      ((hcontq.eventually (eventually_gt_nhds hq)).and
        (hcnear.eventually (eventually_lt_nhds (by simp [debt_clip_zero]; positivity))))
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp hall
  have near (K : ℕ) (hK : K ∈ ({2,11,15}:Finset ℕ)) (u : ℝ) (hu : |u| ≤ δ/2) :=
    hnear (show dist u 0 < δ by rw [dist_zero_right,Real.norm_eq_abs]; linarith) K hK
  refine ⟨δ/2,c/2,B,g/2,a,b,by positivity,by positivity,hB,by positivity,?_,?_⟩
  · intro K hK u hu
    have hh := near K hK u hu
    exact ⟨hh.1.le,by linarith only [hh.2.1]⟩
  · intro u v w hu hv hw z
    apply threePlaneSource_margin_perturb _ _ _ _ _ _ c hc hmargin
    · exact (near 2 (by simp) u hu).2.2.le
    · exact (near 11 (by simp) v hv).2.2.le
    · exact (near 15 (by simp) w hw).2.2.le

private lemma debt_core_covers {K : ℕ} (hK : K ≤ 16) :
    mobiusDivisorSelectionPrimes K \ {2} ⊆ mobiusDivisorCoupledTwoCore := by
  intro p hp
  obtain ⟨hp,hp2⟩ := mem_sdiff.mp hp
  obtain ⟨hp,hprime⟩ := mem_filter.mp hp
  have hp15 : p < 15 := by
    have hpK := mem_range.mp hp
    by_contra hn
    have he : p=15 := by omega
    subst p
    norm_num at hprime
  exact mem_erase.mpr ⟨by simpa using hp2,mem_filter.mpr ⟨mem_range.mpr hp15,hprime⟩⟩

private lemma debt_core_budget {M : ℕ} (hM : 16 ≤ M) :
    let D : ℝ := 2^(mobiusDivisorCoupledTwoCore.card+1)*722
    mobiusDivisorSuccessorEnvelope M mobiusDivisorCoupledTwoCore ≤ D*(M:ℝ)^2 ∧
      ∀ T ⊆ mobiusDivisorCoupledTwoCore, mobiusDivisorSelectionEnergy M T ≤ D*(M:ℝ)^2 := by
  let P := mobiusDivisorCoupledTwoCore
  have hp : ∀ p ∈ P,p.Prime ∧ p < M := by
    intro p hp
    obtain ⟨hp,hprime⟩ := mem_filter.mp (mem_erase.mp hp).2
    exact ⟨hprime,by have := mem_range.mp hp; omega⟩
  have bound (T : Finset ℕ) (hT : ∀ p ∈ T,p.Prime ∧ p < M) (hcard : T.card ≤ P.card+1) :
      mobiusDivisorSelectionEnergy M T ≤ (2:ℝ)^(P.card+1)*722*(M:ℝ)^2 := by
    have he := mobiusDivisorSelectionEnergy_le_pow_card M T hT
    rw [mobiusDivisorSelectionEnergy_empty] at he
    have hd := sum_mobiusDivisorDilationChannel_sq_le_quadratic M
    have hpow : (2:ℝ)^T.card ≤ 2^(P.card+1) := by gcongr; norm_num
    calc
      _ ≤ 2^T.card*(722*(M:ℝ)^2) := he.trans (mul_le_mul_of_nonneg_left hd (by positivity))
      _ ≤ 2^(P.card+1)*(722*(M:ℝ)^2) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := by ring
  constructor
  · rw [mobiusDivisorSuccessorEnvelope_le_iff]
    refine ⟨bound P hp (by omega),?_⟩
    intro q hq
    obtain ⟨hq,_⟩ := mem_sdiff.mp hq
    obtain ⟨hq,hprime⟩ := mem_filter.mp hq
    apply bound (insert q P) _ (card_insert_le q P)
    intro p hp'
    rcases mem_insert.mp hp' with rfl|hp'
    · exact ⟨hprime,mem_range.mp hq⟩
    · exact hp p hp'
  · intro T hT
    exact bound T (fun p hpT => hp p (hT hpT)) ((card_le_card hT).trans (Nat.le_succ _))

private lemma debt_pool_geometry :
    ∃ b : ℕ, ∃ c B g a e : ℝ, 16 ≤ b ∧ 0 < c ∧ 0 < B ∧ 0 < g ∧
      ∀ N n : ℕ, 1 ≤ N →
        (∀ K ∈ ({2,11,15}:Finset ℕ), n ≤ (retainedPrimeWitnessWindow 330 b N K).card) →
        let M := 330*(b+1)*N
        let P := mobiusDivisorCoupledTwoCore
        let U := ({2,11,15}:Finset ℕ).biUnion (retainedPrimeWitnessWindow 330 b N)
        let v := fun p => mobiusDivisorTwoPlanePacket M p P
        (∀ p ∈ U, p.Prime ∧ p < M ∧ p ∉ P ∧ 16 ≤ p ∧ M/p ≤ 15 ∧
          ‖v p‖ ≤ B ∧ g+a*(v p).1+e*(v p).2 ≤ 2*(v p).1*(v p).2) ∧
        (∀ L ⊆ U, L.card < n → ∀ z : ℝ × ℝ,
          ∃ p ∈ U,p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖) := by
  obtain ⟨ε,c,B,g,a,e,hε,hc,hB,hg,hpoint,hmargin⟩ := debt_clip_geometry
  obtain ⟨b0,hb0⟩ := exists_nat_gt (480/ε)
  let b := max 16 b0
  have hb : 16 ≤ b := le_max_left _ _
  have hbR : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hbε : 480 ≤ (b:ℝ)*ε := by
    have hh := (div_lt_iff₀ hε).mp hb0
    have hbb : (b0:ℝ) ≤ b := by exact_mod_cast (le_max_right 16 b0)
    nlinarith only [hh,hbb,hε]
  refine ⟨b,c,B,g,a,e,hb,hc,hB,hg,?_⟩
  intro N n hN hsupply
  let M := 330*(b+1)*N
  let P := mobiusDivisorCoupledTwoCore
  let W := retainedPrimeWitnessWindow 330 b N
  let U := ({2,11,15}:Finset ℕ).biUnion W
  let v := fun p => mobiusDivisorTwoPlanePacket M p P
  have hM : 16 ≤ M := by dsimp [M]; nlinarith
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hr : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < M by omega))
  have window (K p : ℕ) (hK : K ∈ ({2,11,15}:Finset ℕ)) (hp : p ∈ W K) :
      p.Prime ∧ p < M ∧ p ∉ P ∧ 16 ≤ p ∧ M/p=K ∧
        |divisorPrimeClipWeight M p| ≤ ε ∧
        mobiusDivisorNormalizedTwoClip K (divisorPrimeClipWeight M p)=v p := by
    have hk : 2 ≤ K ∧ K ≤ 15 ∧ K ∣ 330 := by
      simp only [mem_insert,mem_singleton] at hK
      rcases hK with rfl|rfl|rfl <;> norm_num
    obtain ⟨hpp,hpM,hbp,hquot,hclip⟩ := retainedPrimeWitnessWindow_data hk.1 (by omega)
      (by omega) hk.2.2 hN hp
    have hpP : p ∉ P := by
      intro hpP
      have hh := mem_range.mp (mem_filter.mp (mem_erase.mp hpP).2).1
      omega
    have hw : |divisorPrimeClipWeight M p| ≤ ε := by
      rw [abs_of_nonneg (divisorPrimeClipWeight_nonneg M p hpp.pos)]
      have hkr : (0:ℝ) ≤ K := Nat.cast_nonneg K
      have hkR : (K:ℝ) ≤ 15 := by exact_mod_cast hk.2.1
      have hbound : 2*(K:ℝ)*(K+1) ≤ 480 := by nlinarith only [hkr,hkR]
      change (b:ℝ)*divisorPrimeClipWeight M p ≤ 2*(K:ℝ)*(K+1) at hclip
      nlinarith only [hclip,hbound,hbε,hbR]
    have he := mobiusDivisorNormalizedTwoClip_eq_physical M p hpp.pos (by omega)
    change M/p=K at hquot
    rw [hquot] at he
    exact ⟨hpp,hpM,hpP,by omega,hquot,hw,he⟩
  have data : ∀ p ∈ U, p.Prime ∧ p < M ∧ p ∉ P ∧ 16 ≤ p ∧ M/p ≤ 15 ∧
      ‖v p‖ ≤ B ∧ g+a*(v p).1+e*(v p).2 ≤ 2*(v p).1*(v p).2 := by
    intro p hp
    obtain ⟨K,hK,hp⟩ := mem_biUnion.mp hp
    obtain ⟨hpp,hpM,hpP,hp16,hquot,hw,he⟩ := window K p hK hp
    have hK15 : K ≤ 15 := by
      simp only [mem_insert,mem_singleton] at hK
      rcases hK with rfl|rfl|rfl <;> omega
    have hh := hpoint K hK (divisorPrimeClipWeight M p) hw
    rw [he] at hh
    exact ⟨hpp,hpM,hpP,hp16,by omega,hh⟩
  -- Each window retains a fresh prime until the requested length is reached.
  have direction : ∀ L ⊆ U, L.card < n → ∀ z : ℝ × ℝ,
      ∃ p ∈ U,p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖ := by
    intro L _ hLn z
    have hex (K : ℕ) : ∃ p : ℕ, K ∈ ({2,11,15}:Finset ℕ) → p ∈ W K ∧ p ∉ L := by
      by_cases hK : K ∈ ({2,11,15}:Finset ℕ)
      · have hn : ∃ p ∈ W K,p ∉ L := by
          by_contra hn
          push Not at hn
          have hle := card_le_card hn
          have hc := hsupply K hK
          change n ≤ (W K).card at hc
          omega
        obtain ⟨p,hp,hpn⟩ := hn
        exact ⟨p,fun _ => ⟨hp,hpn⟩⟩
      · exact ⟨0,fun hh => False.elim (hK hh)⟩
    choose prime hprime using hex
    have hp (K : ℕ) (hK : K ∈ ({2,11,15}:Finset ℕ)) := window K (prime K) hK (hprime K hK).1
    have hm := hmargin (divisorPrimeClipWeight M (prime 2))
      (divisorPrimeClipWeight M (prime 11)) (divisorPrimeClipWeight M (prime 15))
      (hp 2 (by simp)).2.2.2.2.2.1 (hp 11 (by simp)).2.2.2.2.2.1
      (hp 15 (by simp)).2.2.2.2.2.1 (-z)
    rw [(hp 2 (by simp)).2.2.2.2.2.2,(hp 11 (by simp)).2.2.2.2.2.2,
      (hp 15 (by simp)).2.2.2.2.2.2] at hm
    simp only [Prod.fst_neg,Prod.snd_neg,norm_neg] at hm
    have out (K : ℕ) (hK : K ∈ ({2,11,15}:Finset ℕ))
        (hdir : c*‖z‖ ≤ -z.1*(v (prime K)).1+-z.2*(v (prime K)).2) :
        ∃ p ∈ U,p ∉ L ∧ z.1*(v p).1+z.2*(v p).2 ≤ -c*‖z‖ :=
      ⟨prime K,mem_biUnion.mpr ⟨K,hK,(hprime K hK).1⟩,(hprime K hK).2,by linarith only [hdir]⟩
    rcases le_max_iff.mp hm with hh|hh
    · exact out 2 (by simp) hh
    · rcases le_max_iff.mp hh with hh|hh
      · exact out 11 (by simp) hh
      · exact out 15 (by simp) hh
  exact ⟨data,direction⟩

/-- Distinct actual primes realize positive inherited covariance with bounded
signed displacement at every prefix. Complete successor energy and every
preparation subset have one uniform quadratic ceiling. -/
theorem eventually_exists_mobiusDivisorPositiveDebtBatches :
    ∃ b : ℕ, ∃ C H g J : ℝ, 16 ≤ b ∧ 0 < C ∧ 0 < H ∧ 0 < g ∧ 0 < J ∧
      ∀ n : ℕ, ∀ᶠ N : ℕ in atTop,
        let M := 330*(b+1)*N
        let P := mobiusDivisorCoupledTwoCore
        (∀ T ⊆ P, mobiusDivisorSelectionEnergy M T ≤ C*(M:ℝ)^2) ∧
        ∃ l : List ℕ, l.Nodup ∧ l.length=n ∧
          l.toFinset ⊆ ({2,11,15}:Finset ℕ).biUnion (retainedPrimeWitnessWindow 330 b N) ∧
          ∀ k ≤ n,
            (|∑ p ∈ (l.take k).toFinset,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅|+
              |∑ p ∈ (l.take k).toFinset,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}| ≤ H*Real.sqrt M) ∧
            mobiusDivisorSuccessorEnvelope M (P ∪ (l.take k).toFinset) ≤ C*(M:ℝ)^2 ∧
            mobiusDivisorExternalTwoCost M (P ∪ (l.take k).toFinset)+
              (g*(k:ℝ)-J)*M ≤ mobiusDivisorExternalTwoCost M P := by
  obtain ⟨b,c,B,g,a,e,hb,hc,hB,hg,hgeometry⟩ := debt_pool_geometry
  let R : ℝ := 4*B^2/c+2*B+c
  let H : ℝ := 2*R
  let J : ℝ := (|a|+|e|)*R+1
  let D : ℝ := 2^(mobiusDivisorCoupledTwoCore.card+1)*722
  let C : ℝ := D+2*Real.sqrt D*H+H^2
  have hR : 0 < R := by dsimp [R]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨b,C,H,g,J,hb,hC,hH,hg,hJ,?_⟩
  intro n
  have supply : ∀ᶠ N : ℕ in atTop, ∀ K ∈ ({2,11,15}:Finset ℕ),
      n ≤ (retainedPrimeWitnessWindow 330 b N K).card := by
    rw [eventually_all_finset]
    intro K hK
    have hKA : K ∣ 330 := by
      simp only [mem_insert,mem_singleton] at hK
      rcases hK with rfl|rfl|rfl <;> norm_num
    exact eventually_retainedPrimeWitnessWindow_card_ge (by omega) hKA (by omega) n
  filter_upwards [supply,eventually_ge_atTop (1:ℕ)] with N hsupply hN
  let M := 330*(b+1)*N
  let P := mobiusDivisorCoupledTwoCore
  let W := retainedPrimeWitnessWindow 330 b N
  let U := ({2,11,15}:Finset ℕ).biUnion W
  let v := fun p => mobiusDivisorTwoPlanePacket M p P
  have hM : 16 ≤ M := by dsimp [M]; nlinarith
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hr : 0 < Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < M by omega))
  obtain ⟨data,direction⟩ := hgeometry N n hN hsupply
  change (∀ p ∈ U, p.Prime ∧ p < M ∧ p ∉ P ∧ 16 ≤ p ∧ M/p ≤ 15 ∧
    ‖v p‖ ≤ B ∧ g+a*(v p).1+e*(v p).2 ≤ 2*(v p).1*(v p).2) at data
  obtain ⟨l,hnd,hlen,hsub,hreturn⟩ := exists_planeDisplacement_return_batch v U n 0 B c hB hc
    (fun p hp => (data p hp).2.2.2.2.2.1) direction
  have hbudget := debt_core_budget hM
  have hbudget' : mobiusDivisorSuccessorEnvelope M P ≤ D*(M:ℝ)^2 := hbudget.1
  refine ⟨?_,l,hnd,hlen,hsub,?_⟩
  · intro T hT
    have hh := hbudget.2 T hT
    have hDC : D ≤ C := by
      have hh : 0 ≤ 2 * Real.sqrt D * H + H ^ 2 := by positivity
      dsimp only [C]
      linarith only [hh]
    exact hh.trans (mul_le_mul_of_nonneg_right hDC (sq_nonneg (M:ℝ)))
  · intro k hk
    let L := (l.take k).toFinset
    have hLU : L ⊆ U := by
      intro p hp
      exact hsub (List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hp)))
    have hcard : L.card=k := by
      dsimp [L]
      rw [List.toFinset_card_of_nodup (hnd.take),List.length_take,hlen,Nat.min_eq_left hk]
    have hrad : planeDisplacementRadius (∑ p ∈ L,v p) ≤ R := by
      have hh := hreturn k hk
      simp only [zero_add,planeDisplacementRadius,Prod.fst_zero,Prod.snd_zero,
        zero_pow (by omega : 2 ≠ 0),add_zero,Real.sqrt_zero,zero_sub] at hh
      have hn : -(k:ℝ)*c/4 ≤ R := by
        have ht : 0 ≤ (k:ℝ)*c/4 := by positivity
        linarith only [ht,hR]
      exact hh.trans (max_le le_rfl (by linarith only [hn]))
    have hcoords : |∑ p ∈ L,(v p).1| ≤ R ∧ |∑ p ∈ L,(v p).2| ≤ R := by
      have hh : (planeDisplacementRadius (∑ p ∈ L,v p))^2 ≤ R^2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) hR.le).mpr hrad
      rw [planeDisplacementRadius,Real.sq_sqrt (by positivity),Prod.fst_sum,Prod.snd_sum] at hh
      constructor <;> nlinarith [sq_nonneg (∑ p ∈ L,(v p).1),sq_nonneg (∑ p ∈ L,(v p).2),
        sq_abs (∑ p ∈ L,(v p).1),sq_abs (∑ p ∈ L,(v p).2)]
    have hx : (∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅)=
        Real.sqrt M*(∑ p ∈ L,(v p).1) := by
      simp only [v,mobiusDivisorTwoPlanePacket]
      rw [← sum_div]
      field_simp
    have hy : (∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2})=
        Real.sqrt M*(∑ p ∈ L,(v p).2) := by
      simp only [v,mobiusDivisorTwoPlanePacket]
      rw [← sum_div]
      field_simp
    let X := ∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅
    let Y := ∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2}
    have hdisp : |X|+|Y| ≤ H*Real.sqrt M := by
      dsimp only [X,Y]
      rw [hx,hy,abs_mul,abs_mul,abs_of_pos hr]
      dsimp only [H]
      nlinarith only [mul_le_mul_of_nonneg_left hcoords.1 hr.le,
        mul_le_mul_of_nonneg_left hcoords.2 hr.le]
    have hLdata : ∀ p ∈ L,p.Prime ∧ p < M ∧ p ∉ P ∧ p ≠ 2 := by
      intro p hp
      have hh := data p (hLU hp)
      exact ⟨hh.1,hh.2.1,hh.2.2.1,by have := hh.2.2.2.1; omega⟩
    have hcore : ∀ p ∈ L,mobiusDivisorSelectionPrimes (M/p+1)\{2} ⊆ P := by
      intro p hp
      exact debt_core_covers (by have := (data p (hLU hp)).2.2.2.2.1; omega)
    have hchild : ∀ p ∈ L,∀ q ∈ L,p ≠ q → M/p+1 ≤ q := by
      intro p hp q hq _
      have := (data p (hLU hp)).2.2.2.2.1
      have := (data q (hLU hq)).2.2.2.1
      omega
    refine ⟨hdisp,?_,?_⟩
    · have he := mobiusDivisorSuccessorEnvelope_two_block_reserve_error M P L (by omega) hLdata hcore hchild
      have hres : 0 ≤ min
          (∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^2+(mobiusDivisorInterpolatedFibre M p P {2})^2))
          (∑ p ∈ L,(p:ℝ)*(mobiusDivisorInterpolatedFibre M p P ∅+mobiusDivisorInterpolatedFibre M p P {2})^2) := by positivity
      have hsE : Real.sqrt (mobiusDivisorSuccessorEnvelope M P) ≤ Real.sqrt D*(M:ℝ) := by
        calc
          _ ≤ Real.sqrt (D*(M:ℝ)^2) := Real.sqrt_le_sqrt hbudget'
          _ = _ := by rw [Real.sqrt_mul hD.le,Real.sqrt_sq (Nat.cast_nonneg M)]
      have hsM : Real.sqrt (M:ℝ) ≤ M := by
        apply Real.sqrt_le_iff.mpr
        exact ⟨Nat.cast_nonneg M,by nlinarith⟩
      have hDM : |X|+|Y| ≤ H*(M:ℝ) := hdisp.trans (mul_le_mul_of_nonneg_left hsM hH.le)
      have hlin := mul_le_mul (mul_le_mul_of_nonneg_left hsE (by norm_num : (0:ℝ) ≤ 2))
        hDM (by positivity) (by positivity)
      have hquad := (sq_le_sq₀ (by positivity : 0 ≤ |X|+|Y|) (by positivity : 0 ≤ H*(M:ℝ))).mpr hDM
      change mobiusDivisorSuccessorEnvelope M (P ∪ L)+_ ≤
        mobiusDivisorSuccessorEnvelope M P+2*Real.sqrt (mobiusDivisorSuccessorEnvelope M P)*(|X|+|Y|)+(|X|+|Y|)^2 at he
      change mobiusDivisorSuccessorEnvelope M (P ∪ L) ≤ C*(M:ℝ)^2
      dsimp only [C]
      nlinarith only [he,hres,hbudget',hlin,hquad]
    -- The affine terms telescope to the two bounded displacement coordinates.
    · have hc := sum_le_sum (fun p hp => (data p (hLU hp)).2.2.2.2.2.2)
      simp only [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,hcard] at hc
      have hlinA : -(|a| * R) ≤ a*(∑ p ∈ L,(v p).1) := by
        have hh := mul_le_mul_of_nonneg_left hcoords.1 (abs_nonneg a)
        have hn := neg_abs_le (a*(∑ p ∈ L,(v p).1))
        rw [abs_mul] at hn
        linarith only [hh,hn]
      have hlinE : -(|e| * R) ≤ e*(∑ p ∈ L,(v p).2) := by
        have hh := mul_le_mul_of_nonneg_left hcoords.2 (abs_nonneg e)
        have hn := neg_abs_le (e*(∑ p ∈ L,(v p).2))
        rw [abs_mul] at hn
        linarith only [hh,hn]
      have hcov : g*(k:ℝ)-J ≤ ∑ p ∈ L,2*(v p).1*(v p).2 := by
        dsimp only [J]
        linarith only [hc,hlinA,hlinE]
      have hphysical : (M:ℝ)*(∑ p ∈ L,2*(v p).1*(v p).2)=
          ∑ p ∈ L,2*(p:ℝ)*mobiusDivisorInterpolatedFibre M p P ∅*mobiusDivisorInterpolatedFibre M p P {2} := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p hp
        dsimp only [v,mobiusDivisorTwoPlanePacket]
        have hm := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) M)
        have hp := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) p)
        calc
          _ = 2*(Real.sqrt p)^2*mobiusDivisorInterpolatedFibre M p P ∅*
              mobiusDivisorInterpolatedFibre M p P {2}*((M:ℝ)/(Real.sqrt M)^2) := by ring
          _ = _ := by rw [hm,hp,div_self (by positivity : (M:ℝ) ≠ 0),mul_one]
      have hh := mul_le_mul_of_nonneg_left hcov (Nat.cast_nonneg (α:=ℝ) M)
      rw [hphysical] at hh
      change mobiusDivisorExternalTwoCost M (P ∪ L)+(g*(k:ℝ)-J)*M ≤ mobiusDivisorExternalTwoCost M P
      rw [mobiusDivisorExternalTwoCost_union M P L (by omega) hLdata hcore hchild]
      nlinarith only [hh]


private lemma debt_sqrt_capacity (b : ℕ) (hb : 16 ≤ b) (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, ∀ K ∈ ({2,11,15}:Finset ℕ),
      ⌈A*Real.sqrt (330*(b+1)*N:ℕ)⌉₊ ≤ (retainedPrimeWitnessWindow 330 b N K).card := by
  rw [eventually_all_finset]
  intro K hK
  have ha : 1 ≤ 330/K := by
    simp only [mem_insert,mem_singleton] at hK
    rcases hK with rfl|rfl|rfl <;> norm_num
  let a := 330/K
  have hnat : Tendsto (fun N : ℕ => a*N) atTop atTop :=
    Filter.Tendsto.const_mul_atTop' (by omega : 0 < a) tendsto_id
  have har : 0 < Real.sqrt (a:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<a by omega))
  have ht := ((tendsto_prime_window_card_div_sqrt b (by omega)).comp hnat).const_mul_atTop har
  have hratio : Tendsto (fun N : ℕ =>
      ((retainedPrimeWitnessWindow 330 b N K).card:ℝ)/Real.sqrt N) atTop atTop := by
    convert ht using 1
    funext N
    simp only [retainedPrimeWitnessWindow,Function.comp_def,Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg a)]
    field_simp
    rfl
  filter_upwards [hratio.eventually_ge_atTop ((A+2)*Real.sqrt (330*(b+1):ℕ)),
    eventually_ge_atTop (1:ℕ)] with N hcount hN
  have hr : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<N by omega))
  have hM : (1:ℝ) ≤ (330*(b+1)*N:ℕ) := by exact_mod_cast (show 1≤330*(b+1)*N by nlinarith)
  have hs1 : 1 ≤ Real.sqrt (330*(b+1)*N:ℕ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    simpa using hM
  have hh := (le_div_iff₀ hr).mp hcount
  have he : (A+2)*Real.sqrt (330*(b+1)*N:ℕ) ≤
      ((retainedPrimeWitnessWindow 330 b N K).card:ℝ) := by
    rw [Nat.cast_mul (330*(b+1)) N,Real.sqrt_mul (Nat.cast_nonneg (330*(b+1)))]
    simpa only [mul_assoc] using hh
  have hc := Nat.ceil_lt_add_one (show 0 ≤ A*Real.sqrt (330*(b+1)*N:ℕ) by positivity)
  exact_mod_cast (show (⌈A*Real.sqrt (330*(b+1)*N:ℕ)⌉₊:ℝ) ≤
    (retainedPrimeWitnessWindow 330 b N K).card by nlinarith only [he,hc,hs1])

private lemma debt_receiving_radius_sq (a b s : ℝ) (hs : s ≠ 0) (x y : ℝ) :
    s^2*(planeDisplacementRadius (-a/s+x,-b/s+y))^2 = (a-s*x)^2+(b-s*y)^2 := by
  rw [planeDisplacementRadius,Real.sq_sqrt (by positivity)]
  field_simp
  ring

private lemma debt_radius_coords (z : ℝ × ℝ) {R : ℝ} (hR : 0 ≤ R)
    (h : planeDisplacementRadius z ≤ R) : |z.1| ≤ R ∧ |z.2| ≤ R := by
  have hh : (planeDisplacementRadius z)^2 ≤ R^2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hR).mpr h
  rw [planeDisplacementRadius,Real.sq_sqrt (by positivity)] at hh
  constructor <;> nlinarith [sq_abs z.1,sq_abs z.2,sq_nonneg z.1,sq_nonneg z.2]

/-- One actual batch neutralizes both receiving coordinates and simultaneously
reduces the complete inherited prime-two cost. Its covariance surplus also pays
the raw-energy reserve, and every prefix keeps only a linear energy allowance. -/
theorem eventually_exists_mobiusDivisorJointDebtNeutralization :
    ∃ b : ℕ, ∃ R A C : ℝ, 16 ≤ b ∧ 0 < R ∧ 0 < A ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        let M := 330*(b+1)*N
        let P := mobiusDivisorCoupledTwoCore
        (∀ T ⊆ P,mobiusDivisorSelectionEnergy M T ≤ C*(M:ℝ)^2) ∧
        ∃ l : List ℕ,l.Nodup ∧ l.length=⌈A*Real.sqrt M⌉₊ ∧
          l.toFinset ⊆ ({2,11,15}:Finset ℕ).biUnion (retainedPrimeWitnessWindow 330 b N) ∧
          (∀ k : ℕ,mobiusDivisorSelectionEnergy M (P ∪ (l.take k).toFinset) ≤
            mobiusDivisorSelectionEnergy M P+R^2*M) ∧
          (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) ∅)^2+
            (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) {2})^2 ≤ R^2*M ∧
          mobiusDivisorSelectionEnergy M (P ∪ l.toFinset)+
            (mobiusDivisorSelectionFibre M P ∅)^2+
            (mobiusDivisorSelectionFibre M P {2})^2+M ≤ mobiusDivisorSelectionEnergy M P ∧
          mobiusDivisorExternalTwoCost M (P ∪ l.toFinset)+(M:ℝ)*Real.sqrt M ≤
            mobiusDivisorExternalTwoCost M P := by
  obtain ⟨b,c,B,g,a,e,hb,hc,hB,hg,hgeometry⟩ := debt_pool_geometry
  let D : ℝ := 2^(mobiusDivisorCoupledTwoCore.card+1)*722
  let R : ℝ := 4*B^2/c+2*B+c
  let J : ℝ := (|a|+|e|)*(R+Real.sqrt D)
  let A : ℝ := 4*Real.sqrt D/c+(J+R^2+2)/g+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨b,R,A,D,hb,hR,hA,hD,?_⟩
  filter_upwards [debt_sqrt_capacity b hb A hA,eventually_ge_atTop (1:ℕ)] with N hsupply hN
  let M := 330*(b+1)*N
  let P := mobiusDivisorCoupledTwoCore
  let U := ({2,11,15}:Finset ℕ).biUnion (retainedPrimeWitnessWindow 330 b N)
  let v := fun p => mobiusDivisorTwoPlanePacket M p P
  let s : ℝ := Real.sqrt M
  let n : ℕ := ⌈A*s⌉₊
  have hM : 16 ≤ M := by dsimp [M]; nlinarith
  have hMr : (0:ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have hs : 0 < s := Real.sqrt_pos.mpr hMr
  have hssq : s^2=M := Real.sq_sqrt hMr.le
  have hs1 : 1 ≤ s := by
    change 1 ≤ Real.sqrt (M:ℝ)
    rw [Real.le_sqrt (by norm_num) hMr.le]
    exact_mod_cast (show 1≤M by omega)
  have hn : A*s ≤ (n:ℝ) := Nat.le_ceil _
  obtain ⟨data,direction⟩ := hgeometry N n hN hsupply
  change (∀ p ∈ U, p.Prime ∧ p < M ∧ p ∉ P ∧ 16 ≤ p ∧ M/p ≤ 15 ∧
    ‖v p‖ ≤ B ∧ g+a*(v p).1+e*(v p).2 ≤ 2*(v p).1*(v p).2) at data
  have hprep : ∀ T ⊆ P,mobiusDivisorSelectionEnergy M T ≤ D*(M:ℝ)^2 := (debt_core_budget hM).2
  let x := mobiusDivisorSelectionFibre M P ∅
  let y := mobiusDivisorSelectionFibre M P {2}
  let z0 : ℝ × ℝ := (-x/s,-y/s)
  let z := fun L : Finset ℕ => z0+∑ p ∈ L,v p
  have hpair : x^2+y^2 ≤ D*(M:ℝ)^2 := by
    have hh := sum_mobiusDivisorSelectionFibre_sq_le_energy M P {∅,{2}}
    have hh' : x^2+y^2 ≤ mobiusDivisorSelectionEnergy M P := by simpa [x,y] using hh
    exact hh'.trans (hprep P Subset.rfl)
  obtain ⟨l,hnd,hlen,hsub,hreturn⟩ := exists_planeDisplacement_return_batch
    v U n z0 B c hB hc (fun p hp => (data p hp).2.2.2.2.2.1) direction
  have pdata : ∀ p ∈ l.toFinset,p.Prime ∧ p < M ∧ p ∉ P ∧ p ≠ 2 := by
    intro p hp
    have hh := data p (hsub hp)
    exact ⟨hh.1,hh.2.1,hh.2.2.1,by have := hh.2.2.2.1; omega⟩
  have pcore : ∀ p ∈ l.toFinset,mobiusDivisorSelectionPrimes (M/p+1)\{2} ⊆ P := by
    intro p hp
    exact debt_core_covers (by have := (data p (hsub hp)).2.2.2.2.1; omega)
  have pchild : ∀ p ∈ l.toFinset,∀ q ∈ l.toFinset,p ≠ q → M/p+1 ≤ q := by
    intro p hp q hq _
    have := (data p (hsub hp)).2.2.2.2.1
    have := (data q (hsub hq)).2.2.2.1
    omega
  have coord (L : Finset ℕ) :
      s*(∑ p ∈ L,v p).1=∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅ ∧
      s*(∑ p ∈ L,v p).2=∑ p ∈ L,Real.sqrt p*mobiusDivisorInterpolatedFibre M p P {2} := by
    constructor
    · rw [Prod.fst_sum]
      simp only [v,mobiusDivisorTwoPlanePacket]
      rw [← sum_div]
      change s*(_/s)=_
      field_simp
    · rw [Prod.snd_sum]
      simp only [v,mobiusDivisorTwoPlanePacket]
      rw [← sum_div]
      change s*(_/s)=_
      field_simp
  have physical (L : Finset ℕ) (hL : L ⊆ l.toFinset) :
      (mobiusDivisorSelectionFibre M (P ∪ L) ∅)^2+
        (mobiusDivisorSelectionFibre M (P ∪ L) {2})^2=(M:ℝ)*(planeDisplacementRadius (z L))^2 := by
    have ha := mobiusDivisorSelectionFibre_union_two_child_inactive M P L ∅
      (fun p hp => ⟨(pdata p (hL hp)).1,(pdata p (hL hp)).2.2.1,by simp⟩)
      (fun p hp q hq => pchild p (hL hp) q (hL hq))
    have he := mobiusDivisorSelectionFibre_union_two_child_inactive M P L {2}
      (fun p hp => ⟨(pdata p (hL hp)).1,(pdata p (hL hp)).2.2.1,
        by simpa using (pdata p (hL hp)).2.2.2⟩)
      (fun p hp q hq => pchild p (hL hp) q (hL hq))
    rw [ha,he,← (coord L).1,← (coord L).2]
    symm
    rw [← hssq]
    exact debt_receiving_radius_sq x y s hs.ne' _ _
  have initial : (M:ℝ)*(planeDisplacementRadius z0)^2=x^2+y^2 := by
    simpa only [union_empty,z,sum_empty,add_zero] using (physical ∅ (empty_subset _)).symm
  have hr0 : planeDisplacementRadius z0 ≤ Real.sqrt D*s := by
    have hsq : (planeDisplacementRadius z0)^2 ≤ D*(M:ℝ) := by
      nlinarith only [hpair,initial,hMr]
    have hp : (Real.sqrt D*s)^2=D*(M:ℝ) := by rw [mul_pow,Real.sq_sqrt hD.le,hssq]
    have hz0 : 0 ≤ planeDisplacementRadius z0 := Real.sqrt_nonneg _
    have hprod : 0 ≤ Real.sqrt D*s := mul_nonneg (Real.sqrt_nonneg D) hs.le
    nlinarith only [hsq,hp,hz0,hprod]
  have hdecay : planeDisplacementRadius z0-(n:ℝ)*c/4 ≤ 0 := by
    have hAr : 4*Real.sqrt D/c ≤ A := by
      have hh : 0 ≤ (J+R^2+2)/g := by positivity
      dsimp only [A]
      linarith only [hh]
    have hh := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hAr hs.le).trans hn) hc.le
    have he : (4*Real.sqrt D/c*s)*c=4*(Real.sqrt D*s) := by field_simp
    rw [he] at hh
    linarith only [hr0,hh]
  have hend : planeDisplacementRadius (z l.toFinset) ≤ R := by
    have hh := hreturn n le_rfl
    rw [← hlen,List.take_length,hlen] at hh
    exact hh.trans (max_le le_rfl (hdecay.trans hR.le))
  have hcoords : |(∑ p ∈ l.toFinset,v p).1| ≤ (R+Real.sqrt D)*s ∧
      |(∑ p ∈ l.toFinset,v p).2| ≤ (R+Real.sqrt D)*s := by
    have h0 := debt_radius_coords z0 (by positivity) hr0
    have h1 := debt_radius_coords (z l.toFinset) hR.le hend
    have hx : (∑ p ∈ l.toFinset,v p).1=(z l.toFinset).1-z0.1 := by simp [z]
    have hy : (∑ p ∈ l.toFinset,v p).2=(z l.toFinset).2-z0.2 := by simp [z]
    rw [hx,hy]
    constructor
    · exact (abs_sub _ _).trans (by nlinarith only [h0.1,h1.1,mul_le_mul_of_nonneg_left hs1 hR.le])
    · exact (abs_sub _ _).trans (by nlinarith only [h0.2,h1.2,mul_le_mul_of_nonneg_left hs1 hR.le])
  have hcov : (R^2+2)*s ≤ ∑ p ∈ l.toFinset,2*(v p).1*(v p).2 := by
    have hh := sum_le_sum (fun p hp => (data p (hsub hp)).2.2.2.2.2.2)
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,
      List.toFinset_card_of_nodup hnd,hlen] at hh
    have hx := mul_le_mul_of_nonneg_left hcoords.1 (abs_nonneg a)
    have hy := mul_le_mul_of_nonneg_left hcoords.2 (abs_nonneg e)
    have hx' := neg_abs_le (a*(∑ p ∈ l.toFinset,v p).1)
    have hy' := neg_abs_le (e*(∑ p ∈ l.toFinset,v p).2)
    rw [abs_mul] at hx' hy'
    have hAg : (J+R^2+2)/g ≤ A := by
      have ht : 0 ≤ 4*Real.sqrt D/c := by positivity
      dsimp only [A]
      linarith only [ht]
    have hpay := mul_le_mul_of_nonneg_right ((div_le_iff₀ hg).mp hAg) hs.le
    have hn' := mul_le_mul_of_nonneg_left hn hg.le
    simp only [Prod.fst_sum,Prod.snd_sum] at hx hy hx' hy'
    dsimp only [J] at hpay
    nlinarith only [hh,hx,hy,hx',hy',hpay,hn']
  let V := ∑ p ∈ l.toFinset,2*(p:ℝ)*mobiusDivisorInterpolatedFibre M p P ∅*
    mobiusDivisorInterpolatedFibre M p P {2}
  have hphysical : (M:ℝ)*(∑ p ∈ l.toFinset,2*(v p).1*(v p).2)=V := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    dsimp only [v,mobiusDivisorTwoPlanePacket]
    calc
      _ = 2*(Real.sqrt p)^2*mobiusDivisorInterpolatedFibre M p P ∅*
          mobiusDivisorInterpolatedFibre M p P {2}*((M:ℝ)/(Real.sqrt M)^2) := by ring
      _ = _ := by rw [Real.sq_sqrt hMr.le,Real.sq_sqrt (Nat.cast_nonneg p),div_self hMr.ne',mul_one]
  have hV : (M:ℝ)*((R^2+2)*s) ≤ V := by
    rw [← hphysical]
    exact mul_le_mul_of_nonneg_left hcov hMr.le
  have hreserve : V ≤ ∑ p ∈ l.toFinset,(p:ℝ)*
      ((mobiusDivisorInterpolatedFibre M p P ∅)^2+(mobiusDivisorInterpolatedFibre M p P {2})^2) := by
    apply sum_le_sum
    intro p hp
    have hh := mul_nonneg (Nat.cast_nonneg (α:=ℝ) p)
      (sq_nonneg (mobiusDivisorInterpolatedFibre M p P ∅-mobiusDivisorInterpolatedFibre M p P {2}))
    nlinarith only [hh]
  have energy (L : Finset ℕ) (hL : L ⊆ l.toFinset) :
      mobiusDivisorSelectionEnergy M (P ∪ L)+x^2+y^2+
        (∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^2+
          (mobiusDivisorInterpolatedFibre M p P {2})^2)) =
      mobiusDivisorSelectionEnergy M P+(M:ℝ)*(planeDisplacementRadius (z L))^2 := by
    have he := mobiusDivisorSelectionEnergy_union_two_child_inactive M P L (by omega)
      (fun p hp => pdata p (hL hp)) (fun p hp => pcore p (hL hp))
      (fun p hp q hq => pchild p (hL hp) q (hL hq))
    have hr := debt_receiving_radius_sq x y s hs.ne' (∑ p ∈ L,v p).1 (∑ p ∈ L,v p).2
    rw [hssq,(coord L).1,(coord L).2] at hr
    change (M:ℝ)*(planeDisplacementRadius (z L))^2=_ at hr
    change _=mobiusDivisorSelectionEnergy M P-2*x*_-2*y*_+_+_-_ at he
    linarith only [he,hr]
  have endpoint : (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) ∅)^2+
      (mobiusDivisorSelectionFibre M (P ∪ l.toFinset) {2})^2 ≤ R^2*M := by
    rw [physical _ Subset.rfl]
    exact (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (Real.sqrt_nonneg _) hR.le).mpr hend) hMr.le).trans_eq (mul_comm _ _)
  refine ⟨hprep,l,hnd,hlen,hsub,?_,endpoint,?_,?_⟩
  · intro k
    let L := (l.take k).toFinset
    have hL : L ⊆ l.toFinset := by
      intro p hp
      exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hp))
    have hr : planeDisplacementRadius (z L) ≤ max R (planeDisplacementRadius z0) := by
      by_cases hk : k ≤ n
      · exact (hreturn k hk).trans (max_le_max_left _ (sub_le_self _ (by positivity)))
      · have ht : l.take k=l := List.take_of_length_le (by omega)
        dsimp only [L]
        rw [ht]
        exact hend.trans (le_max_left _ _)
    have he := energy L hL
    have hn : 0 ≤ ∑ p ∈ L,(p:ℝ)*((mobiusDivisorInterpolatedFibre M p P ∅)^2+
        (mobiusDivisorInterpolatedFibre M p P {2})^2) := by positivity
    change mobiusDivisorSelectionEnergy M (P ∪ L) ≤ mobiusDivisorSelectionEnergy M P+R^2*M
    rcases le_total R (planeDisplacementRadius z0) with hl|hl
    · rw [max_eq_right hl] at hr
      have hh := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr hr) hMr.le
      change (M:ℝ)*(planeDisplacementRadius (z L))^2 ≤
        (M:ℝ)*(planeDisplacementRadius z0)^2 at hh
      nlinarith only [he,hh,initial,hn,mul_nonneg (sq_nonneg R) hMr.le]
    · rw [max_eq_left hl] at hr
      have hh := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (Real.sqrt_nonneg _) hR.le).mpr hr) hMr.le
      change (M:ℝ)*(planeDisplacementRadius (z L))^2 ≤ (M:ℝ)*R^2 at hh
      nlinarith only [he,hh,hn,sq_nonneg x,sq_nonneg y]
  · have he := energy l.toFinset Subset.rfl
    have hp := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hs1 (show 0 ≤ R^2+2 by positivity)) hMr.le
    rw [physical _ Subset.rfl] at endpoint
    change _+x^2+y^2+M ≤ _
    nlinarith only [he,hV,hreserve,hp,endpoint,hMr]
  · have he := mobiusDivisorExternalTwoCost_union M P l.toFinset (by omega) pdata pcore pchild
    have hp : (M:ℝ)*s ≤ (M:ℝ)*((R^2+2)*s) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg (sq_nonneg R) hs.le,hs]) hMr.le
    change _+(M:ℝ)*s ≤ _
    change _=mobiusDivisorExternalTwoCost M P-V at he
    linarith only [he,hV,hp]

end RHTower
