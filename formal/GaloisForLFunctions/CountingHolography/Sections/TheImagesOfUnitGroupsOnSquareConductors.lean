import GaloisForLFunctions.CountingHolography.Sections.CommonUnitGroupQuotientsAtCoprimeModuli
import GaloisForLFunctions.CountingHolography.Sections.TheNumeratorAboveSquareRootMultiplicity
import GaloisForLFunctions.CountingHolography.Sections.ReducedOrdinaryPrimeProducts

/-! # Unit group images on the diagonal square conductors

The two reduced moduli have cubic logarithmic size, and passing to their
unit orders changes the log ratio by at most the logarithm of the prime
cutoff. Every homomorphic image common to the two groups has only
quadratic logarithmic size because the moduli are coprime.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset ArithmeticFunction _root_.RHTower

private def q (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)
private def U (n : ℕ) := (q n).num.natAbs
private def V (n : ℕ) := (q n).den
private def L (n : ℕ) := 3*windowEnd ((2*n+1)^2+1)

private theorem q_pos (n : ℕ) : 0 < q n :=
  by
    unfold q ordinaryPrimeGenerator
    exact prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k) : (0:ℚ) < _) _

private theorem U_pos (n : ℕ) : 0 < U n :=
  Int.natAbs_pos.mpr (Rat.num_pos.mpr (q_pos n)).ne'

private theorem V_pos (n : ℕ) : 0 < V n := (q n).den_pos

private theorem L_pos (n : ℕ) : 0 < L n := Nat.mul_pos (by decide)
  (packet_window (n • successorSquareTriple n)).1

private theorem supports (n : ℕ) :
    (U n).primeFactors ∪ (V n).primeFactors ⊆ ordinaryPrimeLags (L n) := by
  intro p hp
  by_contra he
  have h := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) p
  change deningerRatExp (q n) p=if p ∈ ordinaryPrimeLags (L n) then _ else 0 at h
  rw [if_neg he,deningerRatExp_apply] at h
  have heq : (U n).factorization p=(V n).factorization p := by
    change ((U n).factorization p:ℤ)-(V n).factorization p=0 at h
    omega
  rcases mem_union.mp hp with hu|hv
  · obtain ⟨hprime,hd,hn⟩ := Nat.mem_primeFactors.mp hu
    have hpos := hprime.factorization_pos_of_dvd hn hd
    rw [heq] at hpos
    have hdiv := Nat.dvd_gcd hd (Nat.dvd_of_factorization_pos hpos.ne')
    exact hprime.not_dvd_one ((q n).reduced.gcd_eq_one ▸ hdiv)
  · obtain ⟨hprime,hd,hn⟩ := Nat.mem_primeFactors.mp hv
    have hpos := hprime.factorization_pos_of_dvd hn hd
    rw [← heq] at hpos
    have hdiv := Nat.dvd_gcd (Nat.dvd_of_factorization_pos hpos.ne') hd
    exact hprime.not_dvd_one ((q n).reduced.gcd_eq_one ▸ hdiv)

private theorem totient_loss {m K : ℕ} (hm : 0 < m) (hK : 0 < K)
    (h : m.primeFactors ⊆ ordinaryPrimeLags K) :
    0 ≤ Real.log m-Real.log m.totient ∧ Real.log m-Real.log m.totient ≤ Real.log K := by
  have hφ : 0 < (m.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm)
  have hn : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have he := le_cutoff_mul_totient hK (fun p hp => (mem_Icc.mp (mem_filter.mp (h hp)).1).2)
  have hh := Real.log_le_log hn (by exact_mod_cast he : (m:ℝ) ≤ K*(m.totient:ℝ))
  rw [Real.log_mul (Nat.cast_pos.mpr hK).ne' hφ.ne'] at hh
  exact ⟨sub_nonneg.mpr (Real.log_le_log hφ (by exact_mod_cast Nat.totient_le m)),by linarith only [hh]⟩

private theorem price_log (n : ℕ) : Real.log (q n:ℝ)=Real.log (U n)-Real.log (V n) := by
  have h := log_ordinaryPrimeGenerator_den (n • successorSquareTriple n)
  rw [← ordinaryPrimeGenerator_num] at h
  change Real.log (V n)=Real.log (U n)-Real.log (q n:ℝ) at h
  linarith only [h]

/-- Replacing both moduli by the numbers of units changes the original log
price by at most the logarithm of the largest allowed prime. -/
theorem square_unit_order_log_error (n : ℕ) :
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    |(Real.log q.num.natAbs.totient-Real.log q.den.totient)-Real.log (q:ℝ)|≤
      Real.log (3*windowEnd ((2*n+1)^2+1):ℕ) := by
  have h₁ := totient_loss (U_pos n) (L_pos n) (subset_union_left.trans (supports n))
  have h₂ := totient_loss (V_pos n) (L_pos n) (subset_union_right.trans (supports n))
  change |(Real.log (U n).totient-Real.log (V n).totient)-Real.log (q n:ℝ)|≤Real.log (L n)
  rw [price_log,abs_le]
  constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2]

private theorem prime_product_log {m K : ℕ} (hS : m.primeFactors ⊆ ordinaryPrimeLags K)
    (f : ℕ → ℕ) (hf : ∀ p ∈ m.primeFactors, 0 < f p ∧ f p ≤ p) :
    Real.log ((∏ p ∈ m.primeFactors, f p : ℕ):ℝ) ≤ 7*K := by
  rw [Nat.cast_prod,Real.log_prod (fun _ h => (Nat.cast_pos.mpr (hf _ h).1).ne')]
  calc _ ≤ ∑ p ∈ m.primeFactors, vonMangoldt p := sum_le_sum fun p h => by
          rw [vonMangoldt_apply_prime (Nat.prime_of_mem_primeFactors h)]
          exact Real.log_le_log (Nat.cast_pos.mpr (hf p h).1) (by exact_mod_cast (hf p h).2)
    _ ≤ _ := (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => vonMangoldt_nonneg)).trans (ordinaryPrimeLagSums K).1

private theorem residue_log {m K : ℕ} (hS : m.primeFactors ⊆ ordinaryPrimeLags K) :
    Real.log (residueUnitOrder m) ≤ 7*K :=
  prime_product_log hS (fun p => p-1) fun p h => by
    have := (Nat.prime_of_mem_primeFactors h).two_le
    omega

private theorem order_loss {m K : ℕ} (hm : 0 < m) (hS : m.primeFactors ⊆ ordinaryPrimeLags K) :
    0 ≤ Real.log m-Real.log (carmichael m) ∧ Real.log m-Real.log (carmichael m) ≤ Real.log 2+7*K := by
  let A := ∏ p ∈ m.primeFactors, p
  have hA : 0 < A := prod_pos fun p h => (Nat.prime_of_mem_primeFactors h).pos
  have hφ := Nat.totient_pos.mpr hm
  have hExponent : 0 < carmichael m := Nat.pos_of_dvd_of_pos (carmichael_dvd_totient m) hφ
  have hlam := (Nat.le_of_dvd hφ (carmichael_dvd_totient m)).trans (Nat.totient_le m)
  have h₁ := Real.log_le_log (Nat.cast_pos.mpr hExponent) (by exact_mod_cast hlam : (carmichael m:ℝ) ≤ m)
  have h₂ := Nat.le_of_dvd (Nat.mul_pos hA (Nat.mul_pos (by decide : 0 < 2) hExponent))
    (dvd_twice_radical_mul_carmichael hm)
  have h₃ := Real.log_le_log (Nat.cast_pos.mpr hm) (by exact_mod_cast h₂ :
    (m:ℝ) ≤ (A:ℝ)*(2*(carmichael m:ℝ)))
  rw [Real.log_mul (Nat.cast_pos.mpr hA).ne' (by positivity),Real.log_mul two_ne_zero (Nat.cast_pos.mpr hExponent).ne'] at h₃
  have h₄ : Real.log A ≤ 7*K := prime_product_log hS id fun p h => ⟨(Nat.prime_of_mem_primeFactors h).pos,le_rfl⟩
  exact ⟨sub_nonneg.mpr h₁,by linarith only [h₃,h₄]⟩

/-- The actual totient orders have no common divisor of cubic logarithmic
size, even though each separate order has that size. -/
theorem square_gcd_unit_orders (n : ℕ) :
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    Real.log (q.num.natAbs.totient.gcd q.den.totient) ≤ 14*(3*windowEnd ((2*n+1)^2+1):ℕ) := by
  have h₁ := residue_log (subset_union_left.trans (supports n))
  have h₂ := residue_log (subset_union_right.trans (supports n))
  have hp (m : ℕ) : 0 < residueUnitOrder m :=
    prod_pos fun p h => by have := (Nat.prime_of_mem_primeFactors h).two_le; omega
  have hdiv := gcd_totient_dvd_residueUnitOrders (q n).reduced
  change (U n).totient.gcd (V n).totient ∣ residueUnitOrder (U n)*residueUnitOrder (V n) at hdiv
  have hg := Nat.gcd_pos_of_pos_left (V n).totient (Nat.totient_pos.mpr (U_pos n))
  have hcard := Nat.le_of_dvd (Nat.mul_pos (hp _) (hp _)) hdiv
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hg) (by exact_mod_cast hcard :
    (((U n).totient.gcd (V n).totient:ℕ):ℝ) ≤ (residueUnitOrder (U n):ℝ)*residueUnitOrder (V n))
  rw [Real.log_mul (Nat.cast_pos.mpr (hp _)).ne' (Nat.cast_pos.mpr (hp _)).ne'] at hlog
  change Real.log ((U n).totient.gcd (V n).totient) ≤ 14*(L n:ℝ)
  linarith only [h₁,h₂,hlog]

private theorem log_range_le {u v K : ℕ} (hu : 0 < u) (_hv : 0 < v)
    (hS : u.primeFactors ⊆ ordinaryPrimeLags K) {H : Type*} [Group H]
    (f : (ZMod u)ˣ →* H) (hM : ∀ a, (f a)^(carmichael v)=1) :
    Real.log (Nat.card f.range) ≤ Real.log (u.totient.gcd v.totient)+Real.log 2+7*K := by
  letI : NeZero u := ⟨hu.ne'⟩
  letI : Finite f.range := (f.finite_iff_finite_ker_range.mp inferInstance).2
  have hg := Nat.gcd_pos_of_pos_left v.totient (Nat.totient_pos.mpr hu)
  have hres : 0 < residueUnitOrder u := prod_pos fun p h => by
    have := (Nat.prime_of_mem_primeFactors h).two_le
    omega
  have hdiv := (unitHom_range_dvd_of_pow_eq_one hu f hM).trans (Nat.mul_dvd_mul_right
    (Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (carmichael_dvd_totient u))
      ((Nat.gcd_dvd_right _ _).trans (carmichael_dvd_totient v))) _)
  have hcard := Nat.le_of_dvd (Nat.mul_pos hg (Nat.mul_pos (by decide : 0 < 2) hres)) hdiv
  have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.card_pos : 0 < Nat.card f.range))
    (by exact_mod_cast hcard : (Nat.card f.range:ℝ) ≤ (u.totient.gcd v.totient:ℕ)*(2*(residueUnitOrder u:ℝ)))
  rw [Real.log_mul (Nat.cast_pos.mpr hg).ne' (by positivity),
    Real.log_mul two_ne_zero (Nat.cast_pos.mpr hres).ne'] at hh
  linarith only [hh,residue_log hS]

/-- Every joint image annihilated by the opposite Carmichael exponent
has at most quadratic logarithmic size, with no target-rank restriction. -/
theorem square_bounded_exponent_image_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ {H : Type*} [Group H],
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    (∀ f : (ZMod q.num.natAbs)ˣ →* H, (∀ a, (f a)^(carmichael q.den)=1) →
      Real.log (Nat.card f.range) ≤ C*(n:ℝ)^2) ∧
    (∀ f : (ZMod q.den)ˣ →* H, (∀ a, (f a)^(carmichael q.num.natAbs)=1) →
      Real.log (Nat.card f.range) ≤ C*(n:ℝ)^2) := by
  obtain ⟨A,_,hA⟩ := successorSquare_window_bound
  refine ⟨Real.log 2+21*A^2,add_nonneg (Real.log_nonneg (by norm_num)) (by positivity),fun n hn {H} _ => ?_⟩
  have hs := square_gcd_unit_orders n
  change Real.log ((U n).totient.gcd (V n).totient) ≤ 14*(L n:ℝ) at hs
  have hL : (L n:ℝ) ≤ A^2*(n:ℝ)^2 := (hA hn).trans_eq (mul_pow _ _ _)
  have h₂ := le_mul_of_one_le_right (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    (one_le_pow₀ (by exact_mod_cast hn : (1:ℝ) ≤ n) (n := 2))
  constructor
  · intro f hf
    have hh := log_range_le (U_pos n) (V_pos n) (subset_union_left.trans (supports n)) f hf
    exact hh.trans (by linarith only [hs,hL,h₂])
  · intro f hf
    have hh := log_range_le (V_pos n) (U_pos n) (subset_union_right.trans (supports n)) f hf
    rw [Nat.gcd_comm] at hs
    exact hh.trans (by linarith only [hs,hL,h₂])

private theorem kernel_log {u : ℕ} (hu : 0 < u) {H : Type*} [Group H] (f : (ZMod u)ˣ →* H) :
    Real.log (Nat.card f.ker)=Real.log u.totient-Real.log (Nat.card f.range) := by
  letI : NeZero u := ⟨hu.ne'⟩
  letI : Finite f.range := (f.finite_iff_finite_ker_range.mp inferInstance).2
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker] at h
  have he : Nat.card f.ker*Nat.card f.range=u.totient :=
    h.trans (by rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient])
  have hr := congrArg (fun m : ℕ => Real.log (m:ℝ)) he
  rw [Nat.cast_mul,Real.log_mul (Nat.cast_pos.mpr Nat.card_pos).ne' (Nat.cast_pos.mpr Nat.card_pos).ne'] at hr
  linarith only [hr]

private theorem cutoff_log_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ}, 0 < n → Real.log (L n) ≤ K*(n:ℝ)^2 := by
  obtain ⟨A,_,hA⟩ := successorSquare_window_bound
  exact ⟨A^2,sq_nonneg _,fun {n} hn => (Real.log_le_self (by positivity : 0 ≤ (L n:ℝ))).trans
    ((hA hn).trans_eq (mul_pow _ _ _))⟩

/-- Every joint measurement annihilated by the opposite unit exponent
has a kernel of positive cubic logarithmic order. -/
theorem square_bounded_exponent_kernel_lower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ {H : Type*} [Group H],
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    (∀ f : (ZMod q.num.natAbs)ˣ →* H, (∀ a, (f a)^(carmichael q.den)=1) → c*(n:ℝ)^3 ≤ Real.log (Nat.card f.ker)) ∧
    (∀ f : (ZMod q.den)ˣ →* H, (∀ a, (f a)^(carmichael q.num.natAbs)=1) → c*(n:ℝ)^3 ≤ Real.log (Nat.card f.ker)) := by
  obtain ⟨c,H,hc,_,hbig⟩ := successorSquare_both_products_lower
  obtain ⟨C,_,himage⟩ := square_bounded_exponent_image_bound
  obtain ⟨K,_,hK⟩ := cutoff_log_bound
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hbig,eventually_ge_atTop 1,tendsto_natCast_atTop_atTop.eventually_ge_atTop
    (max H (2*(K+C)/c))] with n hl hn hlarge
  have hN := (le_max_left H _).trans hlarge
  have hmul : H*n ≤ (n:ℝ)^2 := by simpa only [sq] using mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg n)
  obtain ⟨hu,hv⟩ := hl (m := n) hmul
  have hs := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp ((le_max_right H _).trans hlarge)) (sq_nonneg (n:ℝ))
  have hur := (totient_loss (U_pos n) (L_pos n) (subset_union_left.trans (supports n))).2.trans (hK hn)
  have hvr := (totient_loss (V_pos n) (L_pos n) (subset_union_right.trans (supports n))).2.trans (hK hn)
  change c*n*(n:ℝ)^2 ≤ Real.log (U n) at hu
  change c*n*(n:ℝ)^2 ≤ Real.log (V n) at hv
  intro Htarget _
  constructor
  · intro f hf
    refine le_trans ?_ (kernel_log (U_pos n) f).symm.le
    linarith only [hu,hur,hs,(himage n hn (H := Htarget)).1 f hf]
  · intro f hf
    refine le_trans ?_ (kernel_log (V_pos n) f).symm.le
    linarith only [hv,hvr,hs,(himage n hn (H := Htarget)).2 f hf]

/-- Both directions between the two unit groups have quadratic log image. -/
theorem square_unit_group_image_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    (∀ f : (ZMod q.num.natAbs)ˣ →* (ZMod q.den)ˣ, Real.log (Nat.card f.range) ≤ C*(n:ℝ)^2) ∧
    (∀ f : (ZMod q.den)ˣ →* (ZMod q.num.natAbs)ˣ, Real.log (Nat.card f.range) ≤ C*(n:ℝ)^2) := by
  obtain ⟨C,hC,h⟩ := square_bounded_exponent_image_bound
  exact ⟨C,hC,fun n hn => ⟨fun f => (h n hn (H := (ZMod (V n))ˣ)).1 f (fun a => pow_carmichael (f a)),
    fun f => (h n hn (H := (ZMod (U n))ˣ)).2 f (fun a => pow_carmichael (f a))⟩⟩

/-- Every map in either direction loses a positive cubic log order in its kernel. -/
theorem square_unit_group_kernel_lower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    (∀ f : (ZMod q.num.natAbs)ˣ →* (ZMod q.den)ˣ, c*(n:ℝ)^3 ≤ Real.log (Nat.card f.ker)) ∧
    (∀ f : (ZMod q.den)ˣ →* (ZMod q.num.natAbs)ˣ, c*(n:ℝ)^3 ≤ Real.log (Nat.card f.ker)) := by
  obtain ⟨c,hc,h⟩ := square_bounded_exponent_kernel_lower
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with n hn
  exact ⟨fun f => (hn (H := (ZMod (V n))ˣ)).1 f (fun a => pow_carmichael (f a)),
    fun f => (hn (H := (ZMod (U n))ˣ)).2 f (fun a => pow_carmichael (f a))⟩

private theorem price_bound_iff (g : ℕ → ℝ) {K : ℝ}
    (hK : ∀ {n : ℕ}, 0 < n → |g n-Real.log (q n:ℝ)|≤K*(n:ℝ)^2) :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ n : ℕ, 0 < n → g n ≤ C*(n:ℝ)^2 := by
  have hpow {B : ℕ} (hB : 0 < B) (n : ℕ) : q n ≤ (B:ℚ)^(n^2) ↔
      Real.log (q n:ℝ) ≤ Real.log B*(n:ℝ)^2 := by
    simpa only [q,one_mul,Nat.cast_one,one_pow,mul_one] using
      generator_le_power_iff (n • successorSquareTriple n) hB 1 n
  rw [riemannHypothesis_iff_diagonal_successorSquare_power]
  constructor
  · rintro ⟨B,hB,h⟩
    refine ⟨Real.log B+K,fun n hn => ?_⟩
    have he := (abs_le.mp (hK hn)).2
    have hh := (hpow hB n).mp (h n hn)
    linarith only [he,hh]
  rintro ⟨C,h⟩
  let B := ⌈Real.exp (C+K)⌉₊
  have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hb := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil (Real.exp (C+K)))
  refine ⟨B,hB,fun n hn => (hpow hB n).mpr ?_⟩
  have he := (abs_le.mp (hK hn)).1
  linarith only [he,h n hn,mul_le_mul_of_nonneg_right hb (sq_nonneg (n:ℝ))]

/-- The one-sided comparison of the two unit counts at quadratic log
precision is equivalent to RH. -/
theorem riemannHypothesis_iff_square_unit_order_bound :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
      Real.log q.num.natAbs.totient-Real.log q.den.totient ≤ C*(n:ℝ)^2 := by
  obtain ⟨K,_,hK⟩ := cutoff_log_bound
  exact price_bound_iff (fun n => Real.log (U n).totient-Real.log (V n).totient)
    (K := K) fun {n} hn => (square_unit_order_log_error n).trans (hK hn)

/-- Replacing the two moduli by the respective maximal orders of a
single unit changes the signed logarithm by at most quadratic size. -/
theorem square_carmichael_log_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    |(Real.log (carmichael q.num.natAbs)-Real.log (carmichael q.den))-Real.log (q:ℝ)|≤C*(n:ℝ)^2 := by
  obtain ⟨A,_,hA⟩ := successorSquare_window_bound
  refine ⟨Real.log 2+7*A^2,add_nonneg (Real.log_nonneg (by norm_num)) (by positivity),fun {n} hn => ?_⟩
  have hU := order_loss (U_pos n) (subset_union_left.trans (supports n))
  have hV := order_loss (V_pos n) (subset_union_right.trans (supports n))
  have hL : (L n:ℝ) ≤ A^2*(n:ℝ)^2 := (hA hn).trans_eq (mul_pow _ _ _)
  have h₁ := le_mul_of_one_le_right (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    (one_le_pow₀ (by exact_mod_cast hn : (1:ℝ) ≤ n) (n := 2))
  change |(Real.log (carmichael (U n))-Real.log (carmichael (V n)))-Real.log (q n:ℝ)|≤_
  rw [price_log,abs_le]
  constructor <;> linarith only [hU.1,hU.2,hV.1,hV.2,h₁,hL]

/-- Comparison of the two maximal cyclic orders at the quadratic
logarithmic scale detects the full Riemann hypothesis. -/
theorem riemannHypothesis_iff_square_carmichael_bound :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
      Real.log (carmichael q.num.natAbs)-Real.log (carmichael q.den) ≤ C*(n:ℝ)^2 := by
  obtain ⟨K,_,hK⟩ := square_carmichael_log_error
  exact price_bound_iff (K := K) (fun n => Real.log (carmichael (U n))-Real.log (carmichael (V n))) hK

end GaloisForLFunctions.CountingHolography.Sections
