import GaloisForLFunctions.CountingHolography.Sections.ThePrimeProfileOfThreeSquareConductors
import GaloisForLFunctions.CountingHolography.Sections.ANegativePrimeWindowAtEveryMultiplicity
import GaloisForLFunctions.CountingHolography.Sections.OneMultiplicityPerSquareConductor

/-!
# The numerator above square-root multiplicity

Primes in a fixed relative neighborhood of the middle square have positive
contact of order one over the conductor parameter. The mesh resolves this
whole band once the squared multiplicity exceeds a constant times that
parameter. On the diagonal the numerator alone has cubic logarithmic growth.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticFunction AbsoluteGeometryOfSpecZ

/-- Positive and negative valuation products have the same square-root
window allowance. Rounding adds at most the Chebyshev mass to the denominator. -/
theorem ordinaryPrimeProduct_height_upper : ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    let L := 3*windowEnd N
    let T := A*(∑ i, |(a i:ℝ)|)^2*Real.sqrt L
    let q := ordinaryPrimeGenerator a
    Real.log q.num.natAbs ≤ T ∧ Real.log q.den ≤ 2*T+7*L := by
  obtain ⟨B,hB,h⟩ := contactMultiplicity_size
  refine ⟨34*B,by linarith only [hB],fun N a => ?_⟩
  let L := 3*windowEnd N
  let S := ordinaryPrimeLags L
  let M := ∑ i, |(a i:ℝ)|
  let C := B*M^2
  let x := contactMultiplicity (packet a) L (resolution a)
  let T := (34*B)*M^2*Real.sqrt L
  have hC : 0 ≤ C := mul_nonneg (zero_le_one.trans hB) (sq_nonneg _)
  have hsize (k : ℕ) : |x k| ≤ C/Real.sqrt k := h N a L (resolution a) k
  have hsum : (∑ k ∈ S, |x k| * vonMangoldt k) ≤ T := by
    calc _ ≤ ∑ k ∈ S, C*(vonMangoldt k/Real.sqrt k) := sum_le_sum fun k _ =>
            (mul_le_mul_of_nonneg_right (hsize k) vonMangoldt_nonneg).trans_eq (by ring)
      _ ≤ C*(34*Real.sqrt L) := by
            rw [← mul_sum]
            exact mul_le_mul_of_nonneg_left (ordinaryPrimeLagSums L).2 hC
      _ = T := by unfold C T; ring
  have hn : Real.log (ordinaryPrimeModulus a) ≤ T := by
    rw [log_ordinaryPrimeModulus]
    have hfloor (k : ℕ) : (⌊x k⌋₊ : ℝ) ≤ |x k| := by
      by_cases hx : x k < 0
      · rw [Nat.floor_of_nonpos hx.le,Nat.cast_zero]
        exact abs_nonneg _
      exact (Nat.floor_le (le_of_not_gt hx)).trans (le_abs_self _)
    change (∑ k ∈ S, (⌊x k⌋₊ : ℝ)*vonMangoldt k) ≤ T
    exact (sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hfloor k) vonMangoldt_nonneg).trans hsum
  have hl : -(T+7*L) ≤ Real.log (ordinaryPrimeGenerator a : ℝ) := by
    rw [log_ordinaryPrimeGenerator]
    have hb : (∑ k ∈ S, -(⌊x k⌋:ℝ)*vonMangoldt k) ≤ ∑ k ∈ S, (|x k|+1)*vonMangoldt k := by
      refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ vonMangoldt_nonneg
      linarith only [Int.lt_floor_add_one (x k),neg_le_abs (x k)]
    simp only [neg_mul,sum_neg_distrib,add_mul,one_mul,sum_add_distrib] at hb
    change -(T+7*L) ≤ ∑ k ∈ S, (⌊x k⌋:ℝ)*vonMangoldt k
    have hw : (∑ k ∈ S, vonMangoldt k) ≤ 7*L := (ordinaryPrimeLagSums L).1
    linarith only [hb,hsum,hw]
  dsimp only
  rw [ordinaryPrimeGenerator_num,log_ordinaryPrimeGenerator_den]
  exact ⟨hn,by change _ ≤ 2*T+7*L; linarith only [hn,hl]⟩

/-- Both logarithmic heights have size at most n m² with an additional
n² allowance for denominator rounding, simultaneously at all multiplicities. -/
theorem successorSquare_products_upper : ∃ B : ℝ, 0 ≤ B ∧ ∀ {n m : ℕ}, 0 < n →
    let q := ordinaryPrimeGenerator (m • successorSquareTriple n)
    Real.log q.num.natAbs ≤ B*n*(m:ℝ)^2 ∧ Real.log q.den ≤ B*((n:ℝ)*(m:ℝ)^2+n^2) := by
  obtain ⟨A,hA,hh⟩ := ordinaryPrimeProduct_height_upper
  obtain ⟨K,hK,hL⟩ := successorSquare_window_bound
  let C := 16*A*K
  let B := 2*C+7*K^2
  have hK' := zero_le_one.trans hK
  have hC : 0 ≤ C := by unfold C; positivity
  refine ⟨B,by unfold B; positivity,fun {n m} hn => ?_⟩
  let L := 3*windowEnd ((2*n+1)^2+1)
  let a := m • successorSquareTriple n
  let M := ∑ i, |(a i:ℝ)|
  have H := hh _ a
  have hmass : M ≤ (m:ℝ)*4 := by
    unfold M a
    simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m),← mul_sum]
    exact mul_le_mul_of_nonneg_left (successorSquareTriple_mass n) (Nat.cast_nonneg _)
  have hl : (L:ℝ) ≤ (K*n)^2 := hL hn
  have hsqrt := Real.sqrt_le_sqrt hl
  rw [Real.sqrt_sq (mul_nonneg hK' (Nat.cast_nonneg _))] at hsqrt
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) hmass 2) hA)
    hsqrt (Real.sqrt_nonneg _) (mul_nonneg hA (sq_nonneg _))
  have hamb : A*M^2*Real.sqrt L ≤ C*n*(m:ℝ)^2 := hp.trans_eq (by unfold C; ring)
  change Real.log (ordinaryPrimeGenerator a).num.natAbs ≤ A*M^2*Real.sqrt L ∧
    Real.log (ordinaryPrimeGenerator a).den ≤ 2*(A*M^2*Real.sqrt L)+7*L at H
  have hBC : 2*C ≤ B := le_add_of_nonneg_right (by positivity)
  have hBK : 7*K^2 ≤ B := le_add_of_nonneg_left (by positivity)
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC (Nat.cast_nonneg (α := ℝ) n)) (sq_nonneg (m:ℝ))
  have hsmall := mul_le_mul_of_nonneg_right hBK (sq_nonneg (n:ℝ))
  have hcpos := mul_nonneg (mul_nonneg hC (Nat.cast_nonneg (α := ℝ) n)) (sq_nonneg (m:ℝ))
  dsimp only
  constructor <;> linarith only [H.1,H.2,hamb,hl,hmul,hsmall,hcpos]

private theorem contact_in_middle_band :
    ∃ F c C : ℝ, 1 < F ∧ F ≤ 2 ∧ 0 < c ∧ 1 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ {m k : ℕ}, C*n ≤ (m:ℝ)^2 →
        (n:ℝ)^2 < k → (k:ℝ) ≤ F*(n:ℝ)^2 →
        c*(m:ℝ)^2/n ≤
          (⌊contactMultiplicity (packet (m • successorSquareTriple n)) (3*windowEnd ((2*n+1)^2+1))
            (resolution (m • successorSquareTriple n)) k⌋₊ : ℝ) := by
  obtain ⟨δ,c,hδ,_,hc,hband⟩ := successorSquare_positive_band
  obtain ⟨E,hE,hmesh⟩ := contactMultiplicity_uniform_error
  let F := min (Real.exp δ) 2
  let C := max 1 (4/c)
  let M := 2*E/c
  have hM : 0 ≤ M := div_nonneg (by positivity) hc.le
  have hF : 1 < F := lt_min (Real.one_lt_exp_iff.mpr hδ) one_lt_two
  have hC : 1 ≤ C := le_max_left _ _
  have hninf := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  refine ⟨F,c/4,C,hF,min_le_right _ _,by positivity,hC,?_⟩
  filter_upwards [eventually_ge_atTop ⌈M^2⌉₊,eventually_ge_atTop 1,
    hninf.eventually_gt_atTop (Real.exp (8+Real.log 9))] with n hNM hn hcut
  intro m k hmn hk hkF
  let r := resolution (m • successorSquareTriple n)
  let L := 3*windowEnd ((2*n+1)^2+1)
  let d := successorSquareTriple n
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hk' : (0:ℝ) < k := (sq_pos_of_pos hn').trans hk
  have hnC : (n:ℝ) ≤ C*n := le_mul_of_one_le_left hn'.le hC
  have hm2 := hnC.trans hmn
  have hm' : 0 < m := by
    by_contra! hz
    have h0 : m = 0 := Nat.eq_zero_of_le_zero hz
    simp only [h0,Nat.cast_zero,zero_pow two_ne_zero] at hm2
    exact hn'.not_ge hm2
  have hr := successorSquare_resolution_ge n m
  have hr' : (m:ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : 0 < r := hm'.trans_le hr
  have hMr : M ≤ (r:ℝ) := by
    have hMM : M^2 ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNM)
    exact (le_of_pow_le_pow_left₀ two_ne_zero (Nat.cast_nonneg (α := ℝ) m) (hMM.trans hm2)).trans hr'
  have hE' : E/r ≤ c/2 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hrpos)).mpr
    have hmrc := (div_le_iff₀ hc).mp hMr
    linarith only [hmrc]
  have hl : 8+Real.log 9 < Real.log k :=
    (Real.lt_log_iff_exp_lt hk').mpr (hcut.trans hk)
  have hg : |Real.log ((n:ℝ)^2)-Real.log k| ≤ δ := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log (sq_pos_of_pos hn') hk.le))]
    have hh := Real.log_le_log hk' (hkF.trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)))
    rw [Real.log_mul (Real.exp_pos _).ne' (sq_pos_of_pos hn').ne',Real.log_exp] at hh
    linarith only [hh]
  have hprof := hband hn hl hg
  have hs := (abs_le.mp (hmesh _ d (successorSquareTriple_mass n) hrpos (Nat.cast_pos.mp hk'))).1
  have hsqrt := Real.sqrt_pos.mpr hk'
  have hsample : c/Real.sqrt k ≤ contactMultiplicity (packet d) L r k := by
    have hmul := mul_le_mul_of_nonneg_left hE' (by positivity : 0 ≤ 2/Real.sqrt k)
    change -(2/Real.sqrt k*(E/r)) ≤ contactMultiplicity (packet d) L r k-integratedContact d k at hs
    calc c/Real.sqrt k = 2/Real.sqrt k*c-2/Real.sqrt k*(c/2) := by ring
      _ ≤ integratedContact d k-2/Real.sqrt k*(E/r) := sub_le_sub hprof hmul
      _ ≤ _ := by linarith only [hs]
  have hk2 : Real.sqrt k ≤ 2*n := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    exact hkF.trans ((mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
      (by nlinarith only [sq_nonneg (n:ℝ)]))
  have hraw : c*(m:ℝ)^2/(2*n) ≤ contactMultiplicity (packet (m • d)) L r k := by
    rw [packet_smul,contactMultiplicity_scale]
    have hh := (div_le_div_of_nonneg_left hc.le hsqrt hk2).trans hsample
    exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hh (sq_nonneg (m:ℝ)))
  have htwo : 2 ≤ c*(m:ℝ)^2/(2*n) := by
    apply (le_div_iff₀ (mul_pos two_pos hn')).mpr
    have hh := (mul_le_mul_of_nonneg_right (le_max_right 1 (4/c)) hn'.le).trans hmn
    have hh' := mul_le_mul_of_nonneg_left hh hc.le
    have he : c*((4/c)*n) = 4*n := by field_simp
    rw [he] at hh'
    linarith only [hh']
  let z := contactMultiplicity (packet (m • d)) L r k
  have hz := Nat.lt_floor_add_one z
  change c/4*(m:ℝ)^2/n ≤ (⌊z⌋₊:ℝ)
  change c*(m:ℝ)^2/(2*n) ≤ z at hraw
  have hid : c/4*(m:ℝ)^2/n = (c*(m:ℝ)^2/(2*n))/2 := by ring
  rw [hid]
  linarith only [hz,hraw,htwo]

/-- For all large conductors the reduced numerator has log at least a
constant times n m² throughout the range m² ≥ C n. -/
theorem successorSquare_numerator_lower :
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, C*n ≤ (m:ℝ)^2 →
      c*n*(m:ℝ)^2 ≤ Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n)).num.natAbs := by
  obtain ⟨F,c,C,hF,hF',hc,hC,hmid⟩ := contact_in_middle_band
  have hinf := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  have hmass := hinf.eventually (proportional_prime_mass (u := 1) one_pos hF)
  refine ⟨c*((F-1)/2),C,mul_pos hc (half_pos (sub_pos.mpr hF)),hC,?_⟩
  filter_upwards [hmid,hmass,eventually_ge_atTop 1] with n hband hsum hn
  intro m hmn
  let U := (Ioc ⌊(n:ℝ)^2⌋₊ ⌊F*(n:ℝ)^2⌋₊).filter Nat.Prime
  let L := 3*windowEnd ((2*n+1)^2+1)
  let S := (Icc 2 L).filter Nat.Prime
  let d := m • successorSquareTriple n
  let v := fun k : ℕ => (⌊contactMultiplicity (packet d) L (resolution d) k⌋₊ : ℝ)
  let A := c*(m:ℝ)^2/n
  have hA : 0 ≤ A := by unfold A; positivity
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hmem {k : ℕ} (hk : k ∈ U) : k.Prime ∧ (n:ℝ)^2 < k ∧ (k:ℝ) ≤ F*(n:ℝ)^2 := by
    obtain ⟨h,hp⟩ := mem_filter.mp hk
    obtain ⟨hl,hu⟩ := mem_Ioc.mp h
    exact ⟨hp,(Nat.floor_lt (sq_nonneg _)).mp hl,
      (Nat.cast_le.mpr hu).trans (Nat.floor_le (mul_nonneg (zero_le_one.trans hF.le) (sq_nonneg _)))⟩
  have hs : U ⊆ S := by
    intro k hk
    obtain ⟨hp,_,hu⟩ := hmem hk
    have hW := successorSquareWindowScale_bounds n
    have hb : (k:ℝ) ≤ 3*(windowEnd ((2*n+1)^2+1):ℝ) := by
      have hnn := hW.1.trans hW.2.2
      linarith only [hu,mul_le_mul_of_nonneg_right hF' (sq_nonneg (n:ℝ)),hnn,
        Nat.cast_nonneg (α := ℝ) (windowEnd ((2*n+1)^2+1))]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,by exact_mod_cast hb⟩,hp⟩
  have hh : (F-1)/2*(n:ℝ)^2 ≤ ∑ k ∈ U, Real.log k := by simpa only [one_mul,Function.comp_apply,U] using hsum
  rw [ordinaryPrimeGenerator_num,log_ordinaryPrimeModulus]
  calc c*((F-1)/2)*n*(m:ℝ)^2 = A*((F-1)/2*(n:ℝ)^2) := by unfold A; field_simp
    _ ≤ A*∑ k ∈ U, Real.log k := mul_le_mul_of_nonneg_left hh hA
    _ ≤ ∑ k ∈ U, v k*vonMangoldt k := by
      rw [mul_sum]
      refine sum_le_sum fun k hk => ?_
      obtain ⟨hp,hl,hu⟩ := hmem hk
      have he : Real.log k = vonMangoldt k := by
        rw [← log_contactBase,contactBase,if_pos hp.isPrimePow,hp.minFac_eq]
      rw [he]
      exact mul_le_mul_of_nonneg_right (hband hmn hl hu) vonMangoldt_nonneg
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hs fun k _ _ =>
      mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg

/-- Above the square-root range both coprime parts have logarithm
at least a fixed multiple of n m². -/
theorem successorSquare_both_products_lower :
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, C*n ≤ (m:ℝ)^2 →
      let q := ordinaryPrimeGenerator (m • successorSquareTriple n)
      c*n*(m:ℝ)^2 ≤ Real.log q.num.natAbs ∧ c*n*(m:ℝ)^2 ≤ Real.log q.den := by
  obtain ⟨a,A,ha,hA,hnum⟩ := successorSquare_numerator_lower
  obtain ⟨B,_,herr⟩ := successorSquare_log_negligible (half_pos ha)
  refine ⟨a/2,max A B,half_pos ha,hA.trans (le_max_left _ _),?_⟩
  filter_upwards [hnum,herr] with n hn he
  intro m hmn
  have ha' := hn ((mul_le_mul_of_nonneg_right (le_max_left A B) (Nat.cast_nonneg (α := ℝ) n)).trans hmn)
  have he' := (abs_le.mp (he ((mul_le_mul_of_nonneg_right (le_max_right A B) (Nat.cast_nonneg (α := ℝ) n)).trans hmn))).2
  dsimp only
  rw [log_ordinaryPrimeGenerator_den,← ordinaryPrimeGenerator_num]
  have hpos := mul_nonneg (mul_nonneg ha.le (Nat.cast_nonneg (α := ℝ) n)) (sq_nonneg (m:ℝ))
  constructor <;> linarith only [ha',he',hpos]

/-- The reduced denominator has logarithmic order n² + n m², uniformly
over every positive multiplicity at every sufficiently large conductor. -/
theorem successorSquare_denominator_order :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      let V := Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n)).den
      let H := (n:ℝ)^2 + n*(m:ℝ)^2
      a*H ≤ V ∧ V ≤ b*H := by
  obtain ⟨c,C,hc,hC,hboth⟩ := successorSquare_both_products_lower
  obtain ⟨b,hb,hup⟩ := successorSquare_products_upper
  let a := min (c/2) (1/(12*(1+C)))
  have hCpos := zero_lt_one.trans_le hC
  have ha : 0 < a := lt_min (half_pos hc) (by positivity)
  refine ⟨a,b,ha,hb,?_⟩
  filter_upwards [hboth,successorSquare_denominator_lower,eventually_ge_atTop 1] with n hl hd hn
  intro m hm
  let X := (n:ℝ)^2
  let Y := (n:ℝ)*(m:ℝ)^2
  let V := Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n)).den
  have hx : 0 ≤ X := sq_nonneg _
  have hy : 0 ≤ Y := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  change a*(X+Y) ≤ V ∧ V ≤ b*(X+Y)
  refine ⟨?_,by simpa only [X,Y,V,add_comm] using (hup (m := m) hn).2⟩
  by_cases h : C*n ≤ (m:ℝ)^2
  · have hm' := (le_mul_of_one_le_left (Nat.cast_nonneg (α := ℝ) n) hC).trans h
    have hxy : X ≤ Y := by simpa only [X,Y,sq] using mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg (α := ℝ) n)
    have hv : c*Y ≤ V := by simpa only [V,Y,mul_assoc] using (hl h).2
    calc a*(X+Y) ≤ (c/2)*(X+Y) := mul_le_mul_of_nonneg_right (min_le_left _ _) (add_nonneg hx hy)
      _ ≤ c*Y := by linarith only [mul_le_mul_of_nonneg_left hxy hc.le]
      _ ≤ V := hv
  · have hyx : Y ≤ C*X := by
      have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h) (Nat.cast_nonneg (α := ℝ) n)
      dsimp only [X,Y]
      linarith only [hh]
    have hfit : X+Y ≤ (1+C)*X := by linarith only [hyx]
    have hf : (1/(12*(1+C)))*((1+C)*X) = X/12 := by field_simp
    calc a*(X+Y) ≤ (1/(12*(1+C)))*(X+Y) := mul_le_mul_of_nonneg_right (min_le_right _ _) (add_nonneg hx hy)
      _ ≤ (1/(12*(1+C)))*((1+C)*X) := mul_le_mul_of_nonneg_left hfit (by positivity)
      _ = X/12 := hf
      _ ≤ V := hd m hm

/-- On the RH diagonal every exponential bound with exponent n² eventually
fails for the numerator, including any fixed positive integer base. -/
theorem diagonal_numerator_exceeds_every_quadratic_log (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A*(n:ℝ)^2 <
      Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n)).num.natAbs := by
  obtain ⟨c,C,hc,_,h⟩ := successorSquare_numerator_lower
  filter_upwards [h,tendsto_natCast_atTop_atTop.eventually_gt_atTop (max C (A/c)),
    eventually_ge_atTop 1] with n hn hlarge hpos
  have hC := (le_max_left C (A/c)).trans hlarge.le
  have ha := (div_lt_iff₀ hc).mp ((le_max_right C (A/c)).trans_lt hlarge)
  have hnn := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg (α := ℝ) n)
  rw [← sq] at hnn
  exact (mul_lt_mul_of_pos_right (by linarith only [ha] : A < c*n)
    (sq_pos_of_pos (Nat.cast_pos.mpr hpos))).trans_le (hn hnn)

#print axioms successorSquare_denominator_order
#print axioms successorSquare_both_products_lower
#print axioms diagonal_numerator_exceeds_every_quadratic_log
#print axioms successorSquare_numerator_lower

end GaloisForLFunctions.CountingHolography.Sections
