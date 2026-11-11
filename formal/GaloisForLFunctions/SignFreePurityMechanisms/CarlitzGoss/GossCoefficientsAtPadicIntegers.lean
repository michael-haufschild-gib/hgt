import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TheGossZetaAtNegativeIntegers

/-!
# The coefficients of the Goss zeta function at a `p`-adic integer

For `z ∈ ℤ_p` let `N_k = z mod p^k` (`PadicInt.appr`). The `d`-th coefficient of the Goss zeta
function of `𝔽_q[T]` at `z` is `γ_d(z) = lim_k T^{−d N_k} S_d(N_k)` in `𝔽_p((1/T))` (`gossCoeff`).

* **Convergence.** If `N' = N + p^k c`, then `S_d(N') − T^{d p^k c} S_d(N)` has degree at most
  `d N' − p^k` (`natDegree_gossPoly_sub_le`): it is `∑ aᴺ ((a^{p^k})^c − (T^{d p^k})^c)` and
  `a^{p^k} − T^{d p^k} = (a − T^d)^{p^k}` has degree `≤ (d − 1) p^k`. Hence
  `‖T^{−dN'} S_d(N') − T^{−dN} S_d(N)‖ ≤ ‖T‖^{−p^k}` and the limit exists (`norm_gossCoeff_sub_le`).
* **Stabilization.** For `z ∉ ℕ` the digits of `N_k` grow without bound, so chains of every length
  eventually exist (Erdős–Ginzburg–Ziv). A chain found among the first `k₁` digits bounds the
  greedy prefix value by `p^{k₁}`, and the greedy cost by `2 p^{k₁}`. Thus the exponent
  `κ = d N_k − deg S_d(N_k)` is eventually below `p^k`, and `‖γ_d(z)‖ = ‖T‖^{−κ}`
  (`exists_norm_gossCoeff`).
-/

open Finset Polynomial Filter Topology
open scoped LaurentSeries WithZero

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

open GaloisForLFunctions.RHTower.WeilKloosterman

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The degree bound -/

theorem natDegree_monic_sub_X_pow_le {F : Type*} [Field F] {a : F[X]} {d : ℕ} (ha : a.Monic)
    (hd : a.natDegree = d) : (a - X ^ d).natDegree ≤ d - 1 := by
  by_cases h0 : a - X ^ d = 0
  · rw [h0, natDegree_zero]; exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · rw [pow_zero, eq_one_of_monic_natDegree_zero ha hd, sub_self, natDegree_zero]
  have hlt : (a - X ^ d).degree < a.degree := degree_sub_lt (by
      rw [degree_X_pow, degree_eq_natDegree ha.ne_zero, hd]) ha.ne_zero
    (by rw [ha.leadingCoeff, leadingCoeff_X_pow])
  rw [degree_eq_natDegree h0, degree_eq_natDegree ha.ne_zero, hd, Nat.cast_lt] at hlt
  omega

/-- **The Frobenius congruence of power sums.** Over `𝔽_q` of characteristic `p`,
`deg (S_d(N + p^k c) − T^{d p^k c} S_d(N)) + p^k ≤ d (N + p^k c)` for `d, c ≥ 1`. -/
theorem natDegree_monicPowerSum_sub_le (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]
    [CharP Fq p] {d c : ℕ} (hd : 1 ≤ d) (hc : 1 ≤ c) (N k : ℕ) :
    (monicPowerSum Fq d (N + p ^ k * c) - X ^ (d * (p ^ k * c)) * monicPowerSum Fq d N).natDegree +
      p ^ k ≤ d * (N + p ^ k * c) := by
  have hP : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
  have hbound : (d - 1) * p ^ k + (c - 1) * (d * p ^ k) + N * d + p ^ k =
      d * (N + p ^ k * c) := by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [← hbound, Nat.add_le_add_iff_right, monicPowerSum, monicPowerSum, mul_sum,
    ← sum_sub_distrib]
  refine natDegree_sum_le_of_forall_le _ _ fun a ha => ?_
  obtain ⟨hmon, hdeg⟩ := mem_monicDeg.mp ha
  have hfrob : a ^ p ^ k - (X ^ d) ^ p ^ k = (a - X ^ d) ^ p ^ k :=
    (sub_pow_char_pow a (X ^ d) k).symm
  have hterm : a ^ (N + p ^ k * c) - X ^ (d * (p ^ k * c)) * a ^ N =
      a ^ N * ((∑ i ∈ range c, (a ^ p ^ k) ^ i * ((X ^ d) ^ p ^ k) ^ (c - 1 - i)) *
        (a - X ^ d) ^ p ^ k) := by
    rw [← hfrob, (Commute.all _ _).geom_sum₂_mul c, pow_add, pow_mul a, ← pow_mul (X ^ d),
      ← pow_mul X]
    ring
  rw [hterm]
  have h1 : (a ^ N).natDegree ≤ N * d := natDegree_pow_le.trans (by rw [hdeg])
  have h2 : (∑ i ∈ range c, (a ^ p ^ k) ^ i * ((X ^ d) ^ p ^ k) ^ (c - 1 - i)).natDegree ≤
      (c - 1) * (d * p ^ k) := by
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    have hi' := mem_range.mp hi
    have hx : ((a ^ p ^ k) ^ i).natDegree ≤ i * (d * p ^ k) := by
      rw [← pow_mul]
      refine natDegree_pow_le.trans ?_
      rw [hdeg]
      exact le_of_eq (by ring)
    have hy : ((((X : Fq[X]) ^ d) ^ p ^ k) ^ (c - 1 - i)).natDegree ≤
        (c - 1 - i) * (d * p ^ k) := by
      rw [← pow_mul, ← pow_mul, natDegree_X_pow]
      exact le_of_eq (by ring)
    refine (natDegree_mul_le).trans ((add_le_add hx hy).trans (le_of_eq ?_))
    rw [← add_mul]
    congr 1
    omega
  have h3 : ((a - X ^ d) ^ p ^ k).natDegree ≤ p ^ k * (d - 1) :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_monic_sub_X_pow_le hmon hdeg))
  calc (a ^ N * ((∑ i ∈ range c, (a ^ p ^ k) ^ i * ((X ^ d) ^ p ^ k) ^ (c - 1 - i)) *
        (a - X ^ d) ^ p ^ k)).natDegree
      ≤ (a ^ N).natDegree + ((∑ i ∈ range c, (a ^ p ^ k) ^ i *
          ((X ^ d) ^ p ^ k) ^ (c - 1 - i)).natDegree + ((a - X ^ d) ^ p ^ k).natDegree) :=
        natDegree_mul_le.trans (Nat.add_le_add_left natDegree_mul_le _)
    _ ≤ N * d + ((c - 1) * (d * p ^ k) + p ^ k * (d - 1)) := Nat.add_le_add h1 (Nat.add_le_add h2 h3)
    _ = (d - 1) * p ^ k + (c - 1) * (d * p ^ k) + N * d := by ring

variable {s : ℕ} [NeZero s]

/-- The same degree bound for the recursion over `𝔽_p`, through `𝔽_{p^s}`. -/
theorem natDegree_gossPoly_sub_le {d c : ℕ} (hd : 1 ≤ d) (hc : 1 ≤ c) (N k : ℕ) :
    (gossPoly (ZMod p) (p ^ s) d (N + p ^ k * c) -
        X ^ (d * (p ^ k * c)) * gossPoly (ZMod p) (p ^ s) d N).natDegree + p ^ k ≤
      d * (N + p ^ k * c) := by
  classical
  letI : Fintype (GaloisField p s) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField p s) = p ^ s := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p s (NeZero.ne s)]
  have h := natDegree_monicPowerSum_sub_le (GaloisField p s) hd hc N k
  rw [monicPowerSum_eq_map _ hq, monicPowerSum_eq_map _ hq, ← Polynomial.map_X
    (ZMod.castHom (dvd_refl p) (GaloisField p s)), ← Polynomial.map_pow, ← Polynomial.map_mul,
    ← Polynomial.map_sub, natDegree_map_eq_of_injective (ZMod.castHom _ _).injective] at h
  exact h

/-! ### The normalized power sums in `𝔽_p((1/T))` -/

variable (p s) in
/-- `T^{−dN} S_d(N)`, the sum of `⟨a⟩ ^ N` over monic `a` of degree `d`. -/
noncomputable def normPowerSum (d N : ℕ) : LaurentSeries (ZMod p) :=
  (varT p)⁻¹ ^ (d * N) * aeval (varT p) (gossPoly (ZMod p) (p ^ s) d N)

theorem norm_varT_inv_lt_one : ‖(varT p)⁻¹‖ < 1 := by
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ (one_lt_norm_varT p)

theorem norm_aeval_varT_le (P : (ZMod p)[X]) : ‖aeval (varT p) P‖ ≤ ‖varT p‖ ^ P.natDegree := by
  by_cases hP : P = 0
  · rw [hP, map_zero, norm_zero]; positivity
  · exact (norm_aeval_varT p hP).le

/-- **The Cauchy bound.** `‖T^{−dN'} S_d(N') − T^{−dN} S_d(N)‖ ≤ ‖T‖^{−p^k}` for
`N' = N + p^k c`. -/
theorem norm_normPowerSum_sub_le (d N k c : ℕ) :
    ‖normPowerSum p s d (N + p ^ k * c) - normPowerSum p s d N‖ ≤ ‖(varT p)⁻¹‖ ^ p ^ k := by
  have hT := one_lt_norm_varT p
  have hT0 : varT p ≠ 0 := varT_ne_zero p
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [normPowerSum, gossPoly_zero, zero_mul, pow_zero, map_one, sub_self, norm_zero]
    positivity
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp only [mul_zero, add_zero, sub_self, norm_zero]; positivity
  have hdeg := natDegree_gossPoly_sub_le (p := p) (s := s) hd hc N k
  set N' := N + p ^ k * c
  set P := gossPoly (ZMod p) (p ^ s) d N' - X ^ (d * (p ^ k * c)) * gossPoly (ZMod p) (p ^ s) d N
  have hpow : (varT p)⁻¹ ^ (d * N) = (varT p)⁻¹ ^ (d * N') * varT p ^ (d * (p ^ k * c)) := by
    rw [show d * N' = d * N + d * (p ^ k * c) by simp only [N']; ring, pow_add, mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hT0, one_pow, mul_one]
  have hdiff : normPowerSum p s d N' - normPowerSum p s d N =
      (varT p)⁻¹ ^ (d * N') * aeval (varT p) P := by
    simp only [normPowerSum, P, map_sub, map_mul, map_pow, aeval_X]
    rw [hpow]
    ring
  rw [hdiff, norm_mul, norm_pow, norm_inv]
  have hTpos : 0 < ‖varT p‖ := lt_trans zero_lt_one hT
  calc ‖varT p‖⁻¹ ^ (d * N') * ‖aeval (varT p) P‖
      ≤ ‖varT p‖⁻¹ ^ (d * N') * ‖varT p‖ ^ (d * N' - p ^ k) :=
        mul_le_mul_of_nonneg_left ((norm_aeval_varT_le P).trans
          (pow_le_pow_right₀ hT.le (by omega))) (by positivity)
    _ = ‖varT p‖⁻¹ ^ p ^ k := by
        rw [show d * N' = p ^ k + (d * N' - p ^ k) by omega, pow_add, mul_assoc,
          Nat.add_sub_cancel_left, ← mul_pow, inv_mul_cancel₀ hTpos.ne', one_pow, mul_one]

variable (s) in
/-- The `k`-th approximation `T^{−d N_k} S_d(N_k)`, `N_k = z mod p^k`. -/
noncomputable def coeffSeq (d : ℕ) (z : ℤ_[p]) (k : ℕ) : LaurentSeries (ZMod p) :=
  normPowerSum p s d (z.appr k)

theorem appr_eq_add (z : ℤ_[p]) {k k' : ℕ} (hk : k ≤ k') :
    ∃ c, z.appr k' = z.appr k + p ^ k * c := by
  obtain ⟨c, hc⟩ := PadicInt.dvd_appr_sub_appr z k k' hk
  exact ⟨c, by have := PadicInt.appr_mono z hk; omega⟩

theorem norm_coeffSeq_sub_le (d : ℕ) (z : ℤ_[p]) {k k' : ℕ} (hk : k ≤ k') :
    ‖coeffSeq s d z k' - coeffSeq s d z k‖ ≤ ‖(varT p)⁻¹‖ ^ p ^ k := by
  obtain ⟨c, hc⟩ := appr_eq_add z hk
  simp only [coeffSeq, hc]
  exact norm_normPowerSum_sub_le d _ k c

theorem tendsto_bound :
    Tendsto (fun k => ‖(varT p)⁻¹‖ ^ p ^ k) atTop (𝓝 (0 : ℝ)) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_varT_inv_lt_one).comp
    (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt)

theorem cauchySeq_coeffSeq (d : ℕ) (z : ℤ_[p]) : CauchySeq (coeffSeq s d z) := by
  refine cauchySeq_of_le_tendsto_0 (fun k => 2 * ‖(varT p)⁻¹‖ ^ p ^ k) (fun n m K hn hm => ?_)
    (by simpa only [mul_zero] using tendsto_bound.const_mul 2)
  rw [dist_eq_norm]
  calc ‖coeffSeq s d z n - coeffSeq s d z m‖
      = ‖(coeffSeq s d z n - coeffSeq s d z K) - (coeffSeq s d z m - coeffSeq s d z K)‖ := by
        congr 1; ring
    _ ≤ ‖coeffSeq s d z n - coeffSeq s d z K‖ + ‖coeffSeq s d z m - coeffSeq s d z K‖ :=
        norm_sub_le _ _
    _ ≤ _ := by
        linarith [norm_coeffSeq_sub_le (s := s) d z hn, norm_coeffSeq_sub_le (s := s) d z hm]

variable (s) in
/-- **The coefficient of `x^{−d}` in the Goss zeta function at `z ∈ ℤ_p`**, as an element of
`𝔽_p((1/T))`: `γ_d(z) = lim_k T^{−d N_k} S_d(N_k)`. -/
noncomputable def gossCoeff (d : ℕ) (z : ℤ_[p]) : LaurentSeries (ZMod p) :=
  limUnder atTop (coeffSeq s d z)

theorem tendsto_coeffSeq (d : ℕ) (z : ℤ_[p]) :
    Tendsto (coeffSeq s d z) atTop (𝓝 (gossCoeff s d z)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_coeffSeq d z))

theorem norm_gossCoeff_sub_le (d : ℕ) (z : ℤ_[p]) (k : ℕ) :
    ‖gossCoeff s d z - coeffSeq s d z k‖ ≤ ‖(varT p)⁻¹‖ ^ p ^ k := by
  have hclosed := Metric.isClosed_closedBall (x := coeffSeq s d z k)
    (ε := ‖(varT p)⁻¹‖ ^ p ^ k)
  have hmem := hclosed.mem_of_tendsto (tendsto_coeffSeq d z)
    (eventually_atTop.mpr ⟨k, fun k' hk' => by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact norm_coeffSeq_sub_le d z hk'⟩)
  rwa [Metric.mem_closedBall, dist_eq_norm] at hmem

theorem gossCoeff_zero (z : ℤ_[p]) : gossCoeff s 0 z = 1 := by
  have h : coeffSeq s 0 z = fun _ => 1 := by
    funext k
    simp only [coeffSeq, normPowerSum, zero_mul, pow_zero, gossPoly_zero, map_one, mul_one]
  exact tendsto_nhds_unique (tendsto_coeffSeq 0 z) (by rw [h]; exact tendsto_const_nhds)

/-! ### Digits of the approximations -/

theorem digitsOf_subset {N k c : ℕ} (hN : N < p ^ k) :
    digitsOf p N ⊆ digitsOf p (N + p ^ k * c) := by
  intro x hx
  simp only [digitsOf, mem_filter, mem_product, mem_range, mem_univ, and_true] at hx ⊢
  obtain ⟨hx1, hx2⟩ := hx
  have hdig : 0 < N / p ^ x.1 % p := lt_of_le_of_lt (Nat.zero_le _) hx2
  have hlt : x.1 < k := by
    by_contra hge
    have : N / p ^ x.1 = 0 := Nat.div_eq_of_lt (hN.trans_le
      (Nat.pow_le_pow_right hp.out.pos (by omega)))
    rw [this, Nat.zero_mod] at hdig
    exact lt_irrefl 0 hdig
  refine ⟨by omega, ?_⟩
  have hpk : p ^ k = p ^ x.1 * (p * p ^ (k - x.1 - 1)) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have hsplit : (N + p ^ k * c) / p ^ x.1 = N / p ^ x.1 + p * (p ^ (k - x.1 - 1) * c) := by
    rw [show p ^ k * c = p ^ x.1 * (p * (p ^ (k - x.1 - 1) * c)) by rw [hpk]; ring,
      Nat.add_mul_div_left _ _ (pow_pos hp.out.pos _)]
  rw [hsplit, Nat.add_mul_mod_self_left]
  exact hx2

theorem card_digitsOf_lt_of_lt {N N' : ℕ} (hsub : digitsOf p N ⊆ digitsOf p N') (hne : N ≠ N') :
    (digitsOf p N).card < (digitsOf p N').card := by
  refine card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hne ?_⟩)
  rw [← digitValueNat_digitsOf hp.out.two_le N, ← digitValueNat_digitsOf hp.out.two_le N', heq]

theorem digitsOf_appr_mono (z : ℤ_[p]) {k k' : ℕ} (hk : k ≤ k') :
    digitsOf p (z.appr k) ⊆ digitsOf p (z.appr k') := by
  obtain ⟨c, hc⟩ := appr_eq_add z hk
  rw [hc]
  exact digitsOf_subset (PadicInt.appr_lt z k)

/-- A `p`-adic integer that is not a natural number has infinitely many nonzero digits. -/
theorem exists_appr_ne {z : ℤ_[p]} (hz : z ∉ Set.range (Nat.cast : ℕ → ℤ_[p])) (k : ℕ) :
    ∃ k', k ≤ k' ∧ z.appr k' ≠ z.appr k := by
  by_contra hcon
  push Not at hcon
  apply hz
  refine ⟨z.appr k, ?_⟩
  have hnorm : ∀ n : ℕ, ‖z - (z.appr k : ℤ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ n := by
    intro n
    have hm := PadicInt.appr_spec (max n k) z
    rw [hcon (max n k) (le_max_right _ _)] at hm
    have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr hm
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
    exact h1.trans (pow_le_pow_of_le_one (by positivity)
      (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le)) (le_max_left _ _))
  have h0 : ‖z - (z.appr k : ℤ_[p])‖ = 0 :=
    le_antisymm (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))) hnorm) (norm_nonneg _)
  exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm

theorem exists_card_digitsOf_ge {z : ℤ_[p]} (hz : z ∉ Set.range (Nat.cast : ℕ → ℤ_[p])) (B : ℕ) :
    ∃ k, B ≤ (digitsOf p (z.appr k)).card := by
  induction B with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ B ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨k', hkk', hne⟩ := exists_appr_ne hz k
    exact ⟨k', lt_of_le_of_lt hk (card_digitsOf_lt_of_lt (digitsOf_appr_mono z hkk') hne.symm)⟩

/-- **Erdős–Ginzburg–Ziv chains.** `2 (q − 1) d` digit occurrences contain a chain of length
`d`. -/
theorem nonempty_chain_of_card {S : Finset (Digit p)} (d : ℕ)
    (hS : 2 * (p ^ s - 1) * d ≤ S.card) : Nonempty (DigitChain p s d S) := by
  induction d generalizing S with
  | zero =>
    exact ⟨⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0⟩⟩
  | succ d ih =>
    have hq : 1 ≤ p ^ s - 1 := by
      have := Nat.pow_le_pow_right hp.out.pos (Nat.one_le_iff_ne_zero.mpr (NeZero.ne s))
      have h2 := hp.out.two_le
      have : p ≤ p ^ s := by simpa using this
      omega
    obtain ⟨T, hTS, hTcard, hTdvd⟩ := Int.erdos_ginzburg_ziv (n := p ^ s - 1) (s := S)
      (fun x => (p : ℤ) ^ x.1) (by rw [mul_add, mul_one] at hS; omega)
    have hTne : T.Nonempty := card_pos.mp (by omega)
    have hTdiv : ((p : ℤ) ^ s - 1) ∣ digitValue p T := by
      have h1 : 1 ≤ p ^ s := Nat.one_le_pow _ _ hp.out.pos
      rw [Nat.cast_sub h1] at hTdvd
      push_cast at hTdvd
      exact hTdvd
    obtain ⟨c⟩ := ih (S := S \ T) (by
      rw [card_sdiff_of_subset hTS, hTcard]
      rw [mul_add, mul_one] at hS
      omega)
    exact ⟨DigitChain.cons T hTS hTne hTdiv c⟩

theorem eventually_nonempty_chain {z : ℤ_[p]} (hz : z ∉ Set.range (Nat.cast : ℕ → ℤ_[p]))
    (d : ℕ) : ∃ k₀, ∀ k, k₀ ≤ k → Nonempty (DigitChain p s d (digitsOf p (z.appr k))) := by
  obtain ⟨k₀, hk₀⟩ := exists_card_digitsOf_ge hz (2 * (p ^ s - 1) * d)
  exact ⟨k₀, fun k hk => nonempty_chain_of_card d
    (hk₀.trans (card_le_card (digitsOf_appr_mono z hk)))⟩

/-! ### Stabilization of the norms -/

namespace DigitChain

variable {d : ℕ}

/-- A chain stays a chain in a larger digit collection. -/
def mono {S S' : Finset (Digit p)} (c : DigitChain p s d S) (h : S ⊆ S') : DigitChain p s d S' where
  parts := c.parts
  subset i := (c.subset i).trans h
  disjoint := c.disjoint
  nonempty := c.nonempty
  divisible := c.divisible

omit hp [NeZero s] in
theorem mono_remainder_nonempty {S S' : Finset (Digit p)} (c : DigitChain p s d S) (h : S ⊆ S')
    (hne : S ≠ S') : (c.mono h).remainder.Nonempty := by
  obtain ⟨x, hx', hx⟩ := exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨h, hne⟩)
  refine ⟨x, mem_remainder.mpr ⟨hx', fun i hi => hx (c.subset i hi)⟩⟩

omit hp [NeZero s] in
theorem toComposition_value_last {S : Finset (Digit p)} (c : DigitChain p s d S)
    (hR : c.remainder.Nonempty) :
    (c.toComposition hR).value (Fin.last d) = digitValueNat p c.remainder := by
  simp only [DigitComposition.value, toComposition, Fin.snoc_last, natCast_digitValueNat]

end DigitChain

/-- **The exponent is eventually below `p^k`.** For `z ∉ ℕ` and `d ≥ 1`, eventually
`S_d(N_k) ≠ 0` and `d N_k − deg S_d(N_k) < p^k`. -/
theorem eventually_exponent_lt {z : ℤ_[p]} (hz : z ∉ Set.range (Nat.cast : ℕ → ℤ_[p])) {d : ℕ}
    (hd : 1 ≤ d) : ∃ k₀, ∀ k, k₀ ≤ k →
      gossPoly (ZMod p) (p ^ s) d (z.appr k) ≠ 0 ∧
      d * z.appr k < (gossPoly (ZMod p) (p ^ s) d (z.appr k)).natDegree + p ^ k := by
  obtain ⟨k₁, hk₁⟩ := eventually_nonempty_chain (s := s) hz d
  obtain ⟨c₀⟩ := hk₁ k₁ le_rfl
  obtain ⟨k₂, hk₁₂, hne⟩ := exists_appr_ne hz k₁
  refine ⟨max k₂ (k₁ + 1), fun k hk => ?_⟩
  have hk₂k : k₂ ≤ k := le_of_max_le_left hk
  have hk₁k : k₁ + 1 ≤ k := le_of_max_le_right hk
  set N := z.appr k
  have hsub : digitsOf p (z.appr k₁) ⊆ digitsOf p N := digitsOf_appr_mono z (by omega)
  have hNne : z.appr k₁ ≠ N := by
    intro heq
    have h1 := PadicInt.appr_mono z hk₁₂
    have h2 := PadicInt.appr_mono z hk₂k
    exact hne (le_antisymm (heq ▸ h2) h1)
  have hSne : digitsOf p (z.appr k₁) ≠ digitsOf p N := fun heq =>
    hNne (by rw [← digitValueNat_digitsOf hp.out.two_le (z.appr k₁),
      ← digitValueNat_digitsOf hp.out.two_le N, heq])
  have hR := c₀.mono_remainder_nonempty hsub hSne
  set D := (c₀.mono hsub).toComposition hR
  obtain ⟨G, hG⟩ := DigitComposition.exists_greedy ⟨D⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hdeg := (natDegree_gossPoly_of_greedy (F := ZMod p) hG)
  rw [digitValueNat_digitsOf hp.out.two_le N] at hdeg
  refine ⟨hdeg.1, ?_⟩
  -- the greedy cost is below twice the greedy prefix, which is below the prefix of `D`
  have hcost := hG.prefixCost_lt_twice_prefix hp.out.two_le
  have hlast := hG.last_max D
  have htotalG := digitValue_union G.prefix_disjoint_last
  rw [G.prefix_union_last] at htotalG
  change digitValue p (digitsOf p N) = digitValue p (G.prefixDigits (d' + 1)) +
    G.value (Fin.last (d' + 1)) at htotalG
  have hDlast : D.value (Fin.last (d' + 1)) = digitValueNat p (c₀.mono hsub).remainder :=
    DigitChain.toComposition_value_last _ hR
  have hrem := (c₀.mono hsub).sum_values_add_remainder
  have hc₀ := c₀.sum_values_add_remainder
  have hvals : ∑ i, (c₀.mono hsub).values i = ∑ i, c₀.values i := rfl
  have hlt₁ : digitValueNat p (digitsOf p (z.appr k₁)) < p ^ k₁ := by
    rw [digitValueNat_digitsOf hp.out.two_le]; exact PadicInt.appr_lt z k₁
  have hpow : 2 * p ^ k₁ ≤ p ^ k := by
    calc 2 * p ^ k₁ ≤ p * p ^ k₁ := Nat.mul_le_mul_right _ hp.out.two_le
      _ = p ^ (k₁ + 1) := by ring
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.out.pos hk₁k
  have hNval := digitValueNat_digitsOf hp.out.two_le N
  simp only [DigitComposition.prefixCost] at hcost
  rw [← natCast_digitValueNat, hNval] at htotalG hcost
  have hdegZ := hdeg.2
  have hcastN : digitValueNat p (c₀.mono hsub).remainder + ∑ i, c₀.values i = N := by
    rw [← hvals]; omega
  have hcast : (digitValueNat p (c₀.mono hsub).remainder : ℤ) + ∑ i, (c₀.values i : ℤ) = N := by
    rw [← Nat.cast_sum]; exact_mod_cast hcastN
  have hc₀Z : (∑ i, (c₀.values i : ℤ)) ≤ digitValueNat p (digitsOf p (z.appr k₁)) := by
    exact_mod_cast (by omega : ∑ i, c₀.values i ≤ digitValueNat p (digitsOf p (z.appr k₁)))
  have hpowZ : (2 : ℤ) * p ^ k₁ ≤ p ^ k := by exact_mod_cast hpow
  have hlt₁Z : (digitValueNat p (digitsOf p (z.appr k₁)) : ℤ) < p ^ k₁ := by exact_mod_cast hlt₁
  rw [hDlast] at hlast
  push_cast at hcost htotalG hdegZ ⊢
  nlinarith

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
