import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFineVariationOfTheReciprocalPrimeOctave
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SquareAndSixthPowerSamplesOfTheReciprocalPrimeOctave
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Thinning the power samples of the reciprocal prime octave

The cost of filling gaps in a sampling grid is its maximum gap times
the variation of the reading. The fine variation of the sharp prime
octave costs one logarithm. Consequently, subpower gaps preserve the
square and sixth-power tests for the zero abscissa.
-/

open Finset Filter Topology ArithmeticFunction
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Every index has a selected predecessor within the stated distance. -/
def coversPowerSamples (S : Finset ℕ) (K H : ℕ) : Prop :=
  S ⊆ Icc 1 K ∧ ∀ n ∈ Icc 1 K, ∃ m ∈ S, m≤n ∧ n ≤ m+H

private theorem relative_jump (a b : ℕ) (ha : 1≤a) (hb : a≤b) :
    |reciprocalOctaveError b-reciprocalOctaveError a| ≤ octaveFineVariation b-octaveFineVariation a := by
  induction b,hb using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have hh := abs_add_le (reciprocalOctaveError b-reciprocalOctaveError a) (octaveEndpointJump (b+1))
    have he : reciprocalOctaveError b-reciprocalOctaveError a + octaveEndpointJump (b+1) =
        reciprocalOctaveError (b+1)-reciprocalOctaveError a := by simp only [octaveEndpointJump,Nat.add_sub_cancel]; ring
    rw [he] at hh
    have hstep : octaveFineVariation (b+1) = octaveFineVariation b + |octaveEndpointJump (b+1)| :=
      sum_Ioc_succ_top (f:=fun n => |octaveEndpointJump n|) (ha.trans hb)
    rw [hstep]
    linarith only [hh,ih]

private theorem count_nearby (S : Finset ℕ) (K H : ℕ) (g : ℕ → ℝ) (hg : ∀ m ∈ S, 0≤g m) :
    (∑ n ∈ Icc 1 K, ∑ m ∈ S.filter (fun m => m≤n ∧ n ≤ m+H), g m) ≤
      ((H:ℝ)+1)*∑ m ∈ S, g m := by
  classical
  simp only [sum_filter]
  rw [sum_comm,mul_sum]
  refine sum_le_sum fun m hm => ?_
  let A := (Icc 1 K).filter (fun n => m≤n ∧ n ≤ m+H)
  have hA : A ⊆ Icc m (m+H) := fun n hn => mem_Icc.mpr (mem_filter.mp hn).2
  have hc : A.card ≤ H+1 := by
    have h := card_le_card hA
    rw [Nat.card_Icc] at h
    omega
  rw [←sum_filter,sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hg m hm)

private theorem grid_recovery (S : Finset ℕ) (K H : ℕ) (hS : coversPowerSamples S K H)
    (f V : ℕ → ℝ) (hn : ∀ n, 0≤f n) (hV : Monotone V)
    (hfv : ∀ m n : ℕ, 1 ≤ m → m≤n → f n≤f m+(V n-V m)) :
    (∑ n ∈ Icc 1 K, f n) ≤ ((H:ℝ)+1)*((∑ m ∈ S, f m)+(V (K+1)-V 1)) := by
  let d (j : ℕ) := V (j+1)-V j
  have hd (j : ℕ) : 0≤d j := sub_nonneg.mpr (hV (Nat.le_succ _))
  have tel {a b : ℕ} (hab : a≤b) : ∑ j ∈ Ico a b, d j = V b-V a := by
    induction b,hab using Nat.le_induction with
    | base => simp
    | succ b hb ih => rw [sum_Ico_succ_top hb,ih]; dsimp only [d]; ring
  have point (n : ℕ) (hnK : n ∈ Icc 1 K) :
      f n ≤ (∑ m ∈ S.filter (fun m => m≤n ∧ n ≤ m+H), f m) +
        ∑ j ∈ (Icc 1 K).filter (fun j => j≤n ∧ n≤j+H), d j := by
    obtain ⟨m,hm,hmn,hH⟩ := hS.2 n hnK
    have hm1 := (mem_Icc.mp (hS.1 hm)).1
    have hsub : Ico m n ⊆ (Icc 1 K).filter (fun j => j≤n ∧ n≤j+H) := by
      intro j hj
      have hj' := mem_Ico.mp hj
      have hK := (mem_Icc.mp hnK).2
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by omega,by omega⟩
    apply (hfv m n hm1 hmn).trans
    rw [←tel hmn]
    exact add_le_add (single_le_sum (fun j _ => hn j) (mem_filter.mpr ⟨hm,hmn,hH⟩))
      (sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hd j)
  have h := sum_le_sum point
  rw [sum_add_distrib] at h
  apply h.trans
  rw [mul_add]
  apply add_le_add (count_nearby S K H f fun m _ => hn m)
  have hs : Icc 1 K = Ico 1 (K+1) := by ext n; simp only [mem_Ico,mem_Icc]; omega
  have ht : ∑ j ∈ Icc 1 K, d j = V (K+1)-V 1 := by rw [hs,tel (by omega)]
  rw [←ht]
  exact count_nearby _ _ _ d (fun j _ => hd j)

/-- Exact finite loss for arbitrary, even data-dependent subsamples.
The full variation is charged once per permitted missing predecessor. -/
theorem power_sample_recovery {K H : ℕ} {S : Finset ℕ} (hS : coversPowerSamples S K H)
    (r : ℕ) {ε : ℝ} (he : |ε|=1) :
    powerOctaveSignMass ε r K ≤ ((H:ℝ)+1)*
      ((∑ m ∈ S, max (ε*reciprocalOctaveError (2*m^r)) 0)+octaveFineVariation (2*(K+1)^r)) := by
  let t (n : ℕ) := 2*n^r
  let V (n : ℕ) := octaveFineVariation (t n)
  let f (n : ℕ) := max (ε*reciprocalOctaveError (t n)) 0
  have ht : Monotone t := fun a b h => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
  have hV : Monotone V := fun a b h => sum_le_sum_of_subset_of_nonneg
    (Ioc_subset_Ioc le_rfl (ht h)) (fun _ _ _ => abs_nonneg _)
  have h := grid_recovery S K H hS f V (fun n => le_max_right ..) hV (by
    intro m n hm hmn
    have ht1 : 1≤t m := by dsimp only [t]; have := Nat.one_le_pow r m hm; omega
    have hj := relative_jump _ _ ht1 (ht hmn)
    have hsg := le_abs_self (ε*(reciprocalOctaveError (t n)-reciprocalOctaveError (t m)))
    rw [abs_mul,he,one_mul,mul_sub] at hsg
    apply max_le
    · linarith only [hsg,hj,le_max_left (ε*reciprocalOctaveError (t m)) 0]
    · exact add_nonneg (le_max_right ..) (sub_nonneg.mpr (hV hmn)))
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add_left (sub_le_self _ (sum_nonneg fun _ _ => abs_nonneg _)) _

private theorem variation_log_bound (r K : ℕ) :
    octaveFineVariation (2*(K+1)^r) ≤
      2*(Real.log 2+r*Real.log (K+1)+Real.log 4+4)+Real.log 2 := by
  let n := 2*(K+1)^r
  have hpow : 0<(K+1)^r := pow_pos (Nat.succ_pos _) _
  have h₂ : 2≤n := by dsimp only [n]; omega
  have h := (abs_le.mp (RHTower.Mertens.mertens_first n (by omega))).2
  have he : -Real.log 2 ≤ reciprocalOctaveError n := by
    unfold reciprocalOctaveError
    linarith only [sum_nonneg (s:=Ioc (n/2) n) (fun j _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg j))]
  have hp : 0≤octaveEvenMangoldtPrefix n := sum_nonneg fun j _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hl : Real.log n = Real.log 2+r*Real.log (K+1) := by
    simp only [n,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,
      Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero r (by positivity : (K:ℝ)+1≠0)),Real.log_pow]
  change octaveFineVariation n ≤ _
  rw [octave_fine_variation_identity h₂]
  linarith only [h,he,hp,hl]


/-- A sampling gap may grow faster than any logarithm while remaining
eventually bounded by every positive power. -/
def subpowerSampleGaps (H : ℕ → ℕ) : Prop :=
  ∀ δ : ℝ, 0<δ → ∃ C : ℝ, 0≤C ∧ ∀ᶠ K : ℕ in atTop, (H K:ℝ)+1 ≤ C*(K:ℝ)^δ

/-- Cofinal one-sided masses on the chosen subsets of the power grid. -/
def subpowerSampledOctaves (S : ℕ → Finset ℕ) (r : ℕ) (ε : ℝ) : Prop :=
  ∀ δ : ℝ, 0<δ → ∃ A : ℝ, ∃ᶠ K : ℕ in atTop,
    (∑ m ∈ S K, max (ε*reciprocalOctaveError (2*m^r)) 0) ≤ A*(K:ℝ)^δ

private theorem variation_power_budget (r : ℕ) {δ : ℝ} (hd : 0<δ) :
    ∃ D : ℝ, 0≤D ∧ ∀ K : ℕ, 1≤K → octaveFineVariation (2*(K+1)^r) ≤ D*(K:ℝ)^δ := by
  let L := 2*(Real.log 2+r*Real.log 2+Real.log 4+4)+Real.log 2
  have hL : 0≤L := by dsimp only [L]; positivity
  refine ⟨L+2*r/δ,by positivity,fun K hK => ?_⟩
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  have hk₁ : (1:ℝ)≤K := Nat.one_le_cast.mpr hK
  have h₁ : (1:ℝ)≤(K:ℝ)^δ := Real.one_le_rpow hk₁ hd.le
  have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hk δ)
  rw [Real.log_rpow hk] at hlog
  have hsmall : Real.log K ≤ (K:ℝ)^δ/δ := (le_div_iff₀ hd).mpr (by linarith only [hlog])
  have hs : Real.log ((K:ℝ)+1) ≤ Real.log 2+Real.log K := by
    rw [←Real.log_mul (by norm_num : (2:ℝ)≠0) hk.ne']
    exact Real.log_le_log (by positivity) (by linarith only [hk₁])
  apply (variation_log_bound r K).trans
  calc _ ≤ L + 2*r*Real.log K := by
               dsimp only [L]
               linarith only [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg r : (0:ℝ)≤r)]
       _ ≤ L*(K:ℝ)^δ+2*r*((K:ℝ)^δ/δ) := add_le_add (le_mul_of_one_le_right hL h₁)
               (mul_le_mul_of_nonneg_left hsmall (by positivity))
       _ = _ := by ring

/-- The discarded samples may be chosen separately at every cutoff.
A subpower bound for the largest gap preserves the cofinal zero test. -/
theorem sampled_octaves_iff_full {S : ℕ → Finset ℕ} {H : ℕ → ℕ}
    (cover : ∀ᶠ K : ℕ in atTop, coversPowerSamples (S K) K (H K))
    (gap : subpowerSampleGaps H) (r : ℕ) {ε : ℝ} (he : |ε|=1) :
    subpowerSampledOctaves S r ε ↔ subpowerOctaveGrid r ε := by
  constructor
  · intro h δ hδ
    let d := δ/2
    have hd : 0<d := half_pos hδ
    obtain ⟨A,hA⟩ := h d hd
    obtain ⟨C,hC,hg⟩ := gap d hd
    obtain ⟨D,hD,hv⟩ := variation_power_budget r hd
    refine ⟨C*(max A 0+D),(((hA.and_eventually cover).and_eventually hg).and_eventually
      (eventually_ge_atTop 1)).mono ?_⟩
    rintro K ⟨⟨⟨hprice,hcover⟩,hs⟩,hK⟩
    have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
    have hn := (sum_nonneg (s:=S K) (fun m _ => le_max_right (ε*reciprocalOctaveError (2*m^r)) 0))
    have hv₀ : 0≤octaveFineVariation (2*(K+1)^r) := sum_nonneg fun _ _ => abs_nonneg _
    have hprice' := hprice.trans (mul_le_mul_of_nonneg_right (le_max_left A 0) (Real.rpow_nonneg hk.le d))
    apply (power_sample_recovery hcover r he).trans
    have hprod := mul_le_mul hs (add_le_add hprice' (hv K hK)) (add_nonneg hn hv₀)
      (mul_nonneg hC (Real.rpow_nonneg hk.le d))
    apply hprod.trans_eq
    rw [show δ=d+d by dsimp only [d]; ring,Real.rpow_add hk]
    ring
  · intro h δ hδ
    obtain ⟨A,hA⟩ := h δ hδ
    refine ⟨A,(hA.and_eventually cover).mono fun K hh => ?_⟩
    exact (sum_le_sum_of_subset_of_nonneg hh.2.1 (fun _ _ _ => le_max_right ..)).trans hh.1

/-- Cofinal sampled deficits for the integer gcd products themselves. -/
def subpowerSampledGcd (S : ℕ → Finset ℕ) (r : ℕ) : Prop :=
  ∀ δ : ℝ, 0<δ → ∃ A : ℝ, ∃ᶠ K : ℕ in atTop,
    (∑ m ∈ S K, max (Real.log 2-
      Real.log (octaveGcdProduct (m^r) (m^(r+1)))/(m:ℝ)^(r+1)) 0) ≤ A*(K:ℝ)^δ

private theorem reciprocal_deficit_le_gcd (m r : ℕ) (hm : 0 < m) :
    max ((-1:ℝ)*reciprocalOctaveError (2*m^r)) 0 ≤
      max (Real.log 2-Real.log (octaveGcdProduct (m^r) (m^(r+1)))/(m:ℝ)^(r+1)) 0 := by
  apply max_le_max_right
  have h := (octave_gcd_product_rounding (Nat.pow_pos hm r) (m^(r+1))).1
  have hp : 0<(m:ℝ)^(r+1) := pow_pos (Nat.cast_pos.mpr hm) _
  let A := ∑ j ∈ Ioc (m^r) (2*m^r), vonMangoldt j/j
  change 0≤((m^(r+1):ℕ):ℝ)*A-Real.log (octaveGcdProduct (m^r) (m^(r+1))) at h
  rw [Nat.cast_pow] at h
  have hle := (div_le_iff₀ hp).mpr (show Real.log (octaveGcdProduct (m^r) (m^(r+1))) ≤ A*(m:ℝ)^(r+1) by
    linarith only [h])
  rw [reciprocalOctaveError,show 2*m^r/2=m^r by omega]
  change -1*(A-Real.log 2) ≤ _
  linarith only [hle]

/-- The zeros seen by any power grid are exactly those seen by its
subpower-gap subsample of integer gcd products. -/
theorem sampled_gcd_iff_zero_abscissa {S : ℕ → Finset ℕ} {H : ℕ → ℕ}
    (cover : ∀ᶠ K : ℕ in atTop, coversPowerSamples (S K) K (H K))
    (gap : subpowerSampleGaps H) (s : ℕ) :
    subpowerSampledGcd S (s+2) ↔ _root_.RHTower.zetaZeroAbscissa ≤ ((s:ℝ)+1)/((s:ℝ)+2) := by
  rw [←subpower_octave_grid_iff_abscissa s (by norm_num : |(-1:ℝ)|=1)]
  constructor
  · intro h
    apply (sampled_octaves_iff_full cover gap _ (by norm_num : |(-1:ℝ)|=1)).mp
    intro δ hδ
    obtain ⟨A,hA⟩ := h δ hδ
    refine ⟨A,(hA.and_eventually cover).mono fun K hh => ?_⟩
    exact (sum_le_sum fun m hm => reciprocal_deficit_le_gcd m _ (mem_Icc.mp (hh.2.1 hm)).1).trans hh.1
  · intro h δ hδ
    obtain ⟨A,hA⟩ := (subpower_gcd_grid_iff_octave _).mpr h δ hδ
    refine ⟨A,(hA.and_eventually cover).mono fun K hh => ?_⟩
    exact (sum_le_sum_of_subset_of_nonneg hh.2.1 (fun _ _ _ => le_max_right ..)).trans hh.1

/-- A subpower-gap subsample of square endpoints retains the exact RH criterion. -/
theorem rh_iff_sampled_square_gcd {S : ℕ → Finset ℕ} {H : ℕ → ℕ}
    (cover : ∀ᶠ K : ℕ in atTop, coversPowerSamples (S K) K (H K)) (gap : subpowerSampleGaps H) :
    RiemannHypothesis ↔ subpowerSampledGcd S 2 := by
  rw [riemannHypothesis_iff_square_octave_deficit,subpower_octave_grid_iff_abscissa 0 (by norm_num : |(-1:ℝ)|=1),
    sampled_gcd_iff_zero_abscissa cover gap 0]


/-- Equally spaced indices in a prefix, starting at one. -/
def powerSampleStride (K h : ℕ) : Finset ℕ :=
  (range ((K-1)/h+1)).image (fun j => 1+j*h)

private theorem stride_covers {K h : ℕ} (hK : 1≤K) (hh : 0<h) :
    coversPowerSamples (powerSampleStride K h) K (h-1) := by
  constructor
  · intro m hm
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hm
    have hj' : j ≤ (K-1)/h := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hm' := (Nat.mul_le_mul_right h hj').trans (Nat.div_mul_le_self (K-1) h)
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro n hn
    let j := (n-1)/h
    have hn' := mem_Icc.mp hn
    have hj : j≤(K-1)/h := Nat.div_le_div_right (Nat.sub_le_sub_right hn'.2 1)
    refine ⟨1+j*h,mem_image.mpr ⟨j,mem_range.mpr (Nat.lt_succ_iff.mpr hj),rfl⟩,?_⟩
    have he := Nat.mod_add_div (n-1) h
    rw [Nat.mul_comm h] at he
    have hrem := Nat.mod_lt (n-1) hh
    dsimp only [j]
    omega

theorem powerSampleStride_card (K h : ℕ) (hh : 0<h) :
    (powerSampleStride K h).card=(K-1)/h+1 := by
  rw [powerSampleStride,card_image_of_injective,card_range]
  intro i j he
  exact Nat.eq_of_mul_eq_mul_right hh (Nat.add_left_cancel he)

/-- The binary-logarithmic stride grows to infinity but costs a
subpower factor in every cofinal mass estimate. -/
theorem subpower_binary_gap : subpowerSampleGaps (Nat.log 2) := by
  intro δ hδ
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1+1/(Real.log 2*δ),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  have he : (2:ℝ)^(Nat.log 2 K) ≤ K := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : K≠0)
  have hl := Real.log_le_log (by positivity) he
  rw [Real.log_pow] at hl
  have hh := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hk δ)
  rw [Real.log_rpow hk] at hh
  have hp := Real.one_le_rpow (Nat.one_le_cast.mpr hK : (1:ℝ)≤K) hδ.le
  have hs : (Nat.log 2 K:ℝ) ≤ (K:ℝ)^δ/(Real.log 2*δ) := by
    apply (le_div_iff₀ (mul_pos h₂ hδ)).mpr
    linarith only [mul_le_mul_of_nonneg_right hl hδ.le,hh]
  calc _ ≤ (K:ℝ)^δ/(Real.log 2*δ)+(K:ℝ)^δ := add_le_add hs hp
       _ = _ := by ring

/-- Only one of every binary-length many square/cube gcd products is
needed at each cutoff. This deterministic sample has density tending to zero. -/
theorem rh_iff_binary_stride_square_gcd :
    RiemannHypothesis ↔ subpowerSampledGcd (fun K => powerSampleStride K (Nat.log 2 K+1)) 2 := by
  apply rh_iff_sampled_square_gcd (H:=Nat.log 2) _ subpower_binary_gap
  filter_upwards [eventually_ge_atTop 1] with K hK
  exact stride_covers (h:=Nat.log 2 K+1) hK (Nat.succ_pos _)

/-- Density of the binary-stride sample tends to zero. -/
theorem binary_power_sample_density :
    Tendsto (fun K : ℕ => ((powerSampleStride K (Nat.log 2 K+1)).card:ℝ)/K) atTop (𝓝 0) := by
  have hlog : Tendsto (Nat.log 2) atTop atTop := tendsto_atTop.mpr fun j =>
    (eventually_ge_atTop (2^j)).mono (fun _ h => Nat.le_log_of_pow_le (by decide) h)
  have hh : Tendsto (fun K : ℕ => ((Nat.log 2 K:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop.comp hlog).atTop_add_const_right 1)
  have hi : Tendsto (fun K : ℕ => (K:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hz := hh.add hi
  rw [zero_add] at hz
  apply squeeze_zero' (Eventually.of_forall fun K => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hz
  filter_upwards [eventually_ge_atTop 1] with K hK
  let h := Nat.log 2 K+1
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  have hh' : 0<(h:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have he : (((K-1)/h:ℕ):ℝ) ≤ (K:ℝ)/h :=
    (Nat.cast_div_le (R:=ℝ)).trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le K 1)) hh'.le)
  rw [powerSampleStride_card K _ (Nat.succ_pos _),Nat.cast_add,Nat.cast_one]
  change _ ≤ ((Nat.log 2 K:ℝ)+1)⁻¹+(K:ℝ)⁻¹
  rw [show ((Nat.log 2 K:ℝ)+1)=(h:ℝ) by simp [h]]
  apply (div_le_iff₀ hk).mpr
  field_simp [hh'.ne',hk.ne'] at he ⊢
  linarith only [he]

#print axioms rh_iff_binary_stride_square_gcd
#print axioms binary_power_sample_density
#print axioms sampled_octaves_iff_full
#print axioms sampled_gcd_iff_zero_abscissa
#print axioms rh_iff_sampled_square_gcd
#print axioms power_sample_recovery
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
