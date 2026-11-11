import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.GossCoefficientsAtPadicIntegers
import GaloisForLFunctions.SignFreePurityMechanisms.TheUltrametricNewtonPolygonOfAnEntireSeries

/-!
# The Riemann hypothesis for the Goss zeta function of `𝔽_q[T]`

Let `q = p ^ s`, `L` a complete ultrametric field containing `𝔽_q` (through `τ`) and, isometrically,
`𝔽_p((1/T))` (through `σ`), for instance `ℂ_∞`. For `z ∈ ℤ_p` and a one-unit `u` of `L`,
`u ^ z = lim_k u ^ {z mod p^k}` (`oneUnitPow`; it converges because `u^{p^k} − 1 = (u − 1)^{p^k}` in
characteristic `p`). The Goss zeta function of `𝔽_q[T]` at `(x, −z)` is
`ζ(x, −z) = ∑_d x^{−d} ∑_{a monic, deg a = d} ⟨a⟩ ^ z`, `⟨a⟩ = a / T^d` (`gossZeta`).

* Its coefficients are the images of `γ_d(z) ∈ 𝔽_p((1/T))` (`sum_oneUnitPow_eq`).
* For `z ∉ ℕ`, `‖γ_d(z)‖ = ‖T‖^{−κ_d}` with `κ_d = d N_k − deg S_d(N_k)` for large `k`; the greedy
  Newton polygon makes `κ` strictly convex, and `κ_{d+1} − κ_d ≥ d`. Hence the coefficients form an
  entire series with simple slopes (`entireSimpleSlopes_gossCoeff`).

**Theorem** (`gossZeta_riemannHypothesis`, Sheats). For `z ∉ ℕ` there are `ρ_d ∈ 𝔽_p((1/T))`,
`d ≥ 0`, of strictly decreasing norms, such that in every such `L` the zeros of `x ↦ ζ(x, −z)` are
exactly the `ρ_d`, and each is simple: `‖ζ(x, −z)‖ = C_d ‖x − ρ_d‖` on the sphere `‖x‖ = ‖ρ_d‖`.
For `z = N ∈ ℕ` the function is a polynomial in `1/x` with simple zeros in `𝔽_p((1/T))`
(`gossZetaNeg_eq_prod`).
-/

open Finset Polynomial Filter Topology
open scoped LaurentSeries WithZero

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

open GaloisForLFunctions.RHTower.WeilKloosterman

variable {p : ℕ} [hp : Fact p.Prime]

theorem natDegree_gossPoly_le (R : Type*) [CommRing R] (q : ℕ) :
    ∀ d N, (gossPoly R q d N).natDegree ≤ d * N
  | 0, N => by rw [gossPoly_zero, natDegree_one]; exact Nat.zero_le _
  | d + 1, N => by
    rw [gossPoly_succ, natDegree_neg]
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hj).1)
    refine (natDegree_mul_le).trans ?_
    refine (add_le_add (natDegree_C_mul_X_pow_le _ _) (natDegree_gossPoly_le R q d (N - j))).trans ?_
    calc N - j + d * (N - j) = (d + 1) * (N - j) := by ring
      _ ≤ (d + 1) * N := Nat.mul_le_mul_left _ (Nat.sub_le _ _)

variable {s : ℕ} [NeZero s]

/-! ### The norms of the coefficients -/

theorem norm_coeffSeq (d : ℕ) (z : ℤ_[p]) (k : ℕ)
    (hne : gossPoly (ZMod p) (p ^ s) d (z.appr k) ≠ 0) :
    ‖coeffSeq s d z k‖ = ‖(varT p)⁻¹‖ ^
      (d * z.appr k - (gossPoly (ZMod p) (p ^ s) d (z.appr k)).natDegree) := by
  have hle := natDegree_gossPoly_le (ZMod p) (p ^ s) d (z.appr k)
  have hT := one_lt_norm_varT p
  rw [coeffSeq, normPowerSum, norm_mul, norm_pow, norm_aeval_varT p hne, norm_inv,
    show d * z.appr k = (d * z.appr k - (gossPoly (ZMod p) (p ^ s) d (z.appr k)).natDegree) +
      (gossPoly (ZMod p) (p ^ s) d (z.appr k)).natDegree by omega, pow_add, mul_assoc,
    Nat.add_sub_cancel, ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow, mul_one]

/-- **Stabilization of the norms.** For `z ∉ ℕ`, `‖γ_d(z)‖ = ‖T‖^{−κ}` where eventually
`κ + deg S_d(N_k) = d N_k`. -/
theorem exists_norm_gossCoeff {z : ℤ_[p]} (hz : z ∉ Set.range (Nat.cast : ℕ → ℤ_[p])) (d : ℕ) :
    ∃ κ : ℕ, ‖gossCoeff s d z‖ = ‖(varT p)⁻¹‖ ^ κ ∧ ∃ k₀, ∀ k, k₀ ≤ k →
      gossPoly (ZMod p) (p ^ s) d (z.appr k) ≠ 0 ∧
      κ + (gossPoly (ZMod p) (p ^ s) d (z.appr k)).natDegree = d * z.appr k := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, by rw [gossCoeff_zero, norm_one, pow_zero], 0, fun k _ => ?_⟩
    rw [gossPoly_zero, natDegree_one]
    exact ⟨one_ne_zero, by ring⟩
  obtain ⟨k₀, hk₀⟩ := eventually_exponent_lt (s := s) hz hd
  have ht0 : 0 < ‖(varT p)⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero (varT_ne_zero p))
  have ht1 := norm_varT_inv_lt_one (p := p)
  -- at every large `k` the norm of the limit is that of the approximation
  have hnorm : ∀ k, k₀ ≤ k → ‖gossCoeff s d z‖ = ‖(varT p)⁻¹‖ ^
      (d * z.appr k - (gossPoly (ZMod p) (p ^ s) d (z.appr k)).natDegree) := by
    intro k hk
    obtain ⟨hne, hlt⟩ := hk₀ k hk
    rw [← norm_coeffSeq d z k hne]
    have hclose : ‖gossCoeff s d z - coeffSeq s d z k‖ < ‖coeffSeq s d z k‖ := by
      rw [norm_coeffSeq d z k hne]
      exact (norm_gossCoeff_sub_le d z k).trans_lt
        (pow_lt_pow_right_of_lt_one₀ ht0 ht1 (by omega))
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hclose.ne'
    rw [add_sub_cancel, max_eq_left hclose.le] at this
    exact this
  refine ⟨d * z.appr k₀ - (gossPoly (ZMod p) (p ^ s) d (z.appr k₀)).natDegree, hnorm k₀ le_rfl,
    k₀, fun k hk => ⟨(hk₀ k hk).1, ?_⟩⟩
  have heq := (hnorm k₀ le_rfl).symm.trans (hnorm k hk)
  have hinj := (pow_right_injective₀ ht0 ht1.ne) heq
  have hle := natDegree_gossPoly_le (ZMod p) (p ^ s) d (z.appr k)
  simp only at hinj
  omega

/-- **The Goss coefficients form an entire series with simple slopes.** -/
theorem entireSimpleSlopes_gossCoeff {z : ℤ_[p]} (hz : z ∉ Set.range (Nat.cast : ℕ → ℤ_[p])) :
    EntireSimpleSlopes (fun d => gossCoeff s d z) := by
  choose κ hκ k₀ hk₀ using fun d => exists_norm_gossCoeff (s := s) hz d
  set t := ‖(varT p)⁻¹‖
  have ht0 : 0 < t := norm_pos_iff.mpr (inv_ne_zero (varT_ne_zero p))
  have ht1 : t < 1 := norm_varT_inv_lt_one
  -- strict convexity of the exponents
  have hconv : ∀ d, 2 * κ (d + 1) < κ d + κ (d + 2) := by
    intro d
    obtain ⟨k₃, hk₃⟩ := eventually_nonempty_chain (s := s) hz (d + 2)
    set k := max (max (k₀ d) (k₀ (d + 1))) (max (k₀ (d + 2)) k₃)
    have h0 := (hk₀ d k (by omega)).2
    have h1 := (hk₀ (d + 1) k (by omega)).2
    have h2 := (hk₀ (d + 2) k (by omega)).2
    have hc := natDegree_gossPoly_strictConcave (F := ZMod p) (s := s) (d := d)
      (S := digitsOf p (z.appr k)) (hk₃ k (by omega))
    rw [digitValueNat_digitsOf hp.out.two_le] at hc
    have e1 : (d + 1) * z.appr k = d * z.appr k + z.appr k := by ring
    have e2 : (d + 2) * z.appr k = d * z.appr k + 2 * z.appr k := by ring
    omega
  have hκ0 : κ 0 = 0 := by
    have h := hκ 0
    rw [gossCoeff_zero, norm_one] at h
    exact (pow_eq_one_iff_of_ne_one ht0.le ht1.ne).mp h.symm |>.resolve_right (by
      intro h'; exact absurd h' (by norm_num)) |> fun h => by omega
  have hgrow : ∀ d, κ d + d ≤ κ (d + 1) := by
    intro d
    induction d with
    | zero => rw [hκ0]; exact Nat.zero_le _
    | succ d ih => have := hconv d; omega
  refine ⟨fun d h0 => ?_, fun d => ?_, fun R => ?_⟩
  · have h := hκ d
    rw [h0, norm_zero] at h
    exact (pow_pos ht0 (κ d)).ne' h.symm
  · rw [hκ, hκ, hκ, ← pow_add, ← pow_mul]
    exact pow_lt_pow_right_of_lt_one₀ ht0 ht1 (by have := hconv d; omega)
  · -- ratio test for `t^{κ_d} (|R| + 1)^d`
    set f : ℕ → ℝ := fun d => t ^ κ d * (|R| + 1) ^ d
    have hfpos : ∀ d, 0 < f d := fun d => mul_pos (pow_pos ht0 _) (by positivity)
    have hratio : ∀ d, f (d + 1) / f d ≤ t ^ d * (|R| + 1) := by
      intro d
      rw [div_le_iff₀ (hfpos d)]
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (hgrow d)
      simp only [f, hj, pow_add, pow_succ]
      have : t ^ j ≤ t ^ d := pow_le_pow_of_le_one ht0.le ht1.le (by omega)
      have hR : 0 ≤ |R| + 1 := by positivity
      calc t ^ κ d * t ^ d * t ^ j * ((|R| + 1) ^ d * (|R| + 1))
          ≤ t ^ κ d * t ^ d * t ^ d * ((|R| + 1) ^ d * (|R| + 1)) := by gcongr
        _ = t ^ d * (|R| + 1) * (t ^ κ d * t ^ d * (|R| + 1) ^ d) := by ring
        _ ≤ t ^ d * (|R| + 1) * (t ^ κ d * (|R| + 1) ^ d) := by
          gcongr
          exact mul_le_of_le_one_right (pow_nonneg ht0.le _) (pow_le_one₀ ht0.le ht1.le)
    have hlim : Tendsto (fun d => ‖f (d + 1)‖ / ‖f d‖) atTop (𝓝 0) := by
      have hb : Tendsto (fun d => t ^ d * (|R| + 1)) atTop (𝓝 0) := by
        simpa only [zero_mul] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one ht0.le ht1).mul_const (|R| + 1)
      refine squeeze_zero (fun d => by positivity) (fun d => ?_) hb
      rw [Real.norm_of_nonneg (hfpos _).le, Real.norm_of_nonneg (hfpos _).le]
      exact hratio d
    have hsum := summable_of_ratio_test_tendsto_lt_one zero_lt_one
      (Eventually.of_forall fun d => (hfpos d).ne') hlim
    refine squeeze_zero_norm (fun d => ?_) hsum.tendsto_atTop_zero
    rw [hκ, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (pow_pos ht0 _), abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
      (pow_nonneg ht0.le _)

/-! ### One-unit powers and the zeta function -/

section OneUnits

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]

variable (p) in
/-- `u ^ z = lim_k u ^ (z mod p^k)` for a one-unit `u` and `z ∈ ℤ_p`. -/
noncomputable def oneUnitPow (u : L) (z : ℤ_[p]) : L := limUnder atTop fun k => u ^ z.appr k

theorem norm_eq_one_of_norm_sub_one_lt {u : L} (hu : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (x := (1 : L)) (y := u - 1) (by rw [norm_one]; exact hu.ne')
  rwa [add_sub_cancel, norm_one, max_eq_left hu.le] at h

theorem norm_pow_appr_sub_le [CharP L p] {u : L} (hu : ‖u - 1‖ < 1) (z : ℤ_[p]) {k k' : ℕ}
    (hk : k ≤ k') : ‖u ^ z.appr k' - u ^ z.appr k‖ ≤ ‖u - 1‖ ^ p ^ k := by
  obtain ⟨c, hc⟩ := appr_eq_add z hk
  have hu1 := norm_eq_one_of_norm_sub_one_lt hu
  set w := u ^ p ^ k
  have hw : w - 1 = (u - 1) ^ p ^ k := by rw [sub_pow_char_pow, one_pow]
  have hw1 : ‖w‖ = 1 := by rw [norm_pow, hu1, one_pow]
  rw [hc, pow_add, pow_mul, ← mul_sub_one, norm_mul, norm_pow, hu1, one_pow, one_mul,
    ← geom_sum_mul, norm_mul, hw, norm_pow]
  refine mul_le_of_le_one_left (by positivity) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_pow, hw1, one_pow]

theorem tendsto_oneUnitPow [CharP L p] [CompleteSpace L] {u : L} (hu : ‖u - 1‖ < 1)
    (z : ℤ_[p]) : Tendsto (fun k => u ^ z.appr k) atTop (𝓝 (oneUnitPow p u z)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  have hb : Tendsto (fun k => ‖u - 1‖ ^ p ^ k) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hu).comp
      (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt)
  refine cauchySeq_of_le_tendsto_0 (fun k => 2 * ‖u - 1‖ ^ p ^ k) (fun n m K hn hm => ?_)
    (by simpa only [mul_zero] using hb.const_mul 2)
  rw [dist_eq_norm]
  calc ‖u ^ z.appr n - u ^ z.appr m‖
      = ‖(u ^ z.appr n - u ^ z.appr K) - (u ^ z.appr m - u ^ z.appr K)‖ := by congr 1; ring
    _ ≤ ‖u ^ z.appr n - u ^ z.appr K‖ + ‖u ^ z.appr m - u ^ z.appr K‖ := norm_sub_le _ _
    _ ≤ _ := by linarith [norm_pow_appr_sub_le hu z hn, norm_pow_appr_sub_le hu z hm]

end OneUnits

variable (p) in
/-- **The Goss zeta function of `𝔽_q[T]`** at `(x, −z)`, `z ∈ ℤ_p`, in a field `L` containing `𝔽_q`
(through `τ`) and `𝔽_p((1/T))` (through `σ`):
`ζ(x, −z) = ∑_d x^{−d} ∑_{a monic, deg a = d} ⟨a⟩ ^ z`, `⟨a⟩ = a(T) / T^d`. -/
noncomputable def gossZeta (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]
    {L : Type*} [NontriviallyNormedField L] (σ : LaurentSeries (ZMod p) →+* L) (τ : Fq →+* L)
    (z : ℤ_[p]) (x : L) : L :=
  ∑' d, x⁻¹ ^ d *
    ∑ a ∈ monicDeg (F := Fq) d, oneUnitPow p (eval₂ τ (σ (varT p)) a / σ (varT p) ^ d) z

section Zeta

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq Fq] [CharP Fq p]
  {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  {σ : LaurentSeries (ZMod p) →+* L} (hσ : ∀ r, ‖σ r‖ = ‖r‖) (τ : Fq →+* L)

include hσ

omit [CompleteSpace L] in
theorem norm_τ_le (c : Fq) : ‖τ c‖ ≤ 1 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, norm_zero]; exact zero_le_one
  have h := congrArg (fun y => ‖τ y‖) (FiniteField.pow_card_sub_one_eq_one c hc)
  simp only [map_pow, norm_pow, map_one, norm_one] at h
  have hq : Fintype.card Fq - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := Fq); omega
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hq).mp h).le

omit [CompleteSpace L] in
theorem norm_eval₂_le (Q : Fq[X]) : ‖eval₂ τ (σ (varT p)) Q‖ ≤ ‖varT p‖ ^ Q.natDegree := by
  have hT := one_lt_norm_varT p
  rw [eval₂_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
  rw [norm_mul, norm_pow, hσ]
  calc ‖τ (Q.coeff i)‖ * ‖varT p‖ ^ i ≤ 1 * ‖varT p‖ ^ i :=
        mul_le_mul_of_nonneg_right (norm_τ_le hσ τ _) (by positivity)
    _ ≤ _ := by rw [one_mul]; exact pow_le_pow_right₀ hT.le (by have := mem_range.mp hi; omega)

omit [CompleteSpace L] in
/-- `⟨a⟩ = a / T^d` is a one-unit. -/
theorem norm_sub_one_lt {d : ℕ} {a : Fq[X]} (ha : a ∈ monicDeg (F := Fq) d) :
    ‖eval₂ τ (σ (varT p)) a / σ (varT p) ^ d - 1‖ < 1 := by
  obtain ⟨hmon, hdeg⟩ := mem_monicDeg.mp ha
  have hT := one_lt_norm_varT p
  have hσT : σ (varT p) ≠ 0 := (map_ne_zero σ).mpr (varT_ne_zero p)
  have heq : eval₂ τ (σ (varT p)) a / σ (varT p) ^ d - 1 =
      eval₂ τ (σ (varT p)) (a - X ^ d) / σ (varT p) ^ d := by
    rw [eval₂_sub, eval₂_X_pow, sub_div, div_self (pow_ne_zero _ hσT)]
  rw [heq, norm_div, norm_pow, hσ, div_lt_one (by positivity)]
  refine (norm_eval₂_le hσ τ _).trans_lt ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [pow_zero, eq_one_of_monic_natDegree_zero hmon hdeg, sub_self, natDegree_zero, pow_zero]
    exact hT
  · exact pow_lt_pow_right₀ hT (lt_of_le_of_lt (natDegree_monic_sub_X_pow_le hmon hdeg)
      (by omega))

omit [CompleteSpace L] in
/-- The finite sums `∑ ⟨a⟩ ^ N` are the images of `T^{−dN} S_d(N)`. -/
theorem sum_pow_eq (hq : Fintype.card Fq = p ^ s) (d N : ℕ) :
    ∑ a ∈ monicDeg (F := Fq) d, (eval₂ τ (σ (varT p)) a / σ (varT p) ^ d) ^ N =
      σ (normPowerSum p s d N) := by
  simp_rw [div_pow]
  rw [← sum_div]
  have hsum : ∑ a ∈ monicDeg (F := Fq) d, eval₂ τ (σ (varT p)) a ^ N =
      eval₂ τ (σ (varT p)) (monicPowerSum Fq d N) := by
    rw [monicPowerSum, eval₂_finsetSum]
    simp only [eval₂_pow]
  rw [hsum, monicPowerSum_eq_map Fq hq, eval₂_map,
    show τ.comp (ZMod.castHom (dvd_refl p) Fq) =
      σ.comp (algebraMap (ZMod p) (LaurentSeries (ZMod p))) from RingHom.ext_zmod _ _,
    ← hom_eval₂, normPowerSum, map_mul, map_pow, map_inv₀, ← pow_mul, div_eq_mul_inv, mul_comm,
    inv_pow, mul_comm d N]
  rfl

theorem isometry_σ : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ hσ

/-- **The coefficients.** `∑_{a monic, deg a = d} ⟨a⟩ ^ z = γ_d(z)`. -/
theorem sum_oneUnitPow_eq (hq : Fintype.card Fq = p ^ s) (d : ℕ) (z : ℤ_[p]) :
    ∑ a ∈ monicDeg (F := Fq) d, oneUnitPow p (eval₂ τ (σ (varT p)) a / σ (varT p) ^ d) z =
      σ (gossCoeff s d z) := by
  haveI : CharP L p := charP_of_injective_ringHom σ.injective p
  have h1 : Tendsto (fun k => ∑ a ∈ monicDeg (F := Fq) d,
      (eval₂ τ (σ (varT p)) a / σ (varT p) ^ d) ^ z.appr k) atTop
      (𝓝 (∑ a ∈ monicDeg (F := Fq) d, oneUnitPow p (eval₂ τ (σ (varT p)) a / σ (varT p) ^ d) z)) :=
    tendsto_finset_sum _ fun a ha => tendsto_oneUnitPow (norm_sub_one_lt hσ τ ha) z
  have h2 : Tendsto (fun k => σ (coeffSeq s d z k)) atTop (𝓝 (σ (gossCoeff s d z))) :=
    ((isometry_σ hσ).continuous.tendsto _).comp (tendsto_coeffSeq d z)
  refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
  rw [coeffSeq, sum_pow_eq hσ τ hq]

/-- The zeta function is the entire series of the images of the coefficients in `1/x`. -/
theorem gossZeta_eq_eval (hq : Fintype.card Fq = p ^ s) (z : ℤ_[p]) (x : L) :
    gossZeta p Fq σ τ z x = EntireSimpleSlopes.eval (fun d => σ (gossCoeff s d z)) x⁻¹ := by
  simp only [gossZeta, EntireSimpleSlopes.eval, sum_oneUnitPow_eq hσ τ hq, mul_comm]

end Zeta

/-! ### The Riemann hypothesis -/

/-- **The Riemann hypothesis for the Goss zeta function of `𝔽_q[T]`** (Sheats), at every
`z ∈ ℤ_p \ ℕ`. There are `ρ_d ∈ 𝔽_p((1/T))`, `d ≥ 0`, nonzero with strictly decreasing norms, such
that for every complete ultrametric field `L ⊇ 𝔽_q` with an isometric copy of `𝔽_p((1/T))`:
the zeros of `x ↦ ζ(x, −z)` in `L` are exactly the `ρ_d`, and each is simple, with
`‖ζ(x, −z)‖ = C_d ‖x − ρ_d‖` on the sphere `‖x‖ = ‖ρ_d‖`. -/
theorem gossZeta_riemannHypothesis {z : ℤ_[p]} (hz : z ∉ Set.range (Nat.cast : ℕ → ℤ_[p])) :
    ∃ ρ : ℕ → LaurentSeries (ZMod p), (∀ d, ρ d ≠ 0) ∧ StrictAnti (fun d => ‖ρ d‖) ∧
      ∀ (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq] [CharP Fq p],
        Fintype.card Fq = p ^ s →
        ∀ (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
          (σ : LaurentSeries (ZMod p) →+* L), (∀ r, ‖σ r‖ = ‖r‖) → ∀ τ : Fq →+* L,
          (∀ x : L, x ≠ 0 → (gossZeta p Fq σ τ z x = 0 ↔ ∃ d, x = σ (ρ d))) ∧
          ∀ d, ∃ C : ℝ, 0 < C ∧ ∀ x : L, ‖x‖ = ‖ρ d‖ →
            ‖gossZeta p Fq σ τ z x‖ = C * ‖x - σ (ρ d)‖ := by
  set γ : ℕ → LaurentSeries (ZMod p) := fun d => gossCoeff s d z
  have hγ : EntireSimpleSlopes γ := entireSimpleSlopes_gossCoeff hz
  choose u hu using fun d => hγ.exists_eval_eq_zero d
  have hrad := hγ.radius_pos
  have hu0 : ∀ d, u d ≠ 0 := fun d h0 => by
    have := (hu d).1
    rw [h0, norm_zero] at this
    exact (hrad d).ne this
  refine ⟨fun d => (u d)⁻¹, fun d => inv_ne_zero (hu0 d), fun d e hde => ?_, ?_⟩
  · simp only [norm_inv, (hu _).1]
    exact inv_strictAnti₀ (hrad d) (hγ.radius_strictMono hde)
  intro Fq _ _ _ _ hq L _ _ _ σ hσ τ
  set a : ℕ → L := fun d => σ (γ d)
  have ha : EntireSimpleSlopes a :=
    ⟨fun d => (map_ne_zero σ).mpr (hγ.ne_zero d), fun d => by simp only [a, hσ]; exact hγ.concave d,
      fun R => by simpa only [a, hσ] using hγ.tendsto R⟩
  have hrad' : ∀ d, EntireSimpleSlopes.radius a d = EntireSimpleSlopes.radius γ d := fun d => by
    simp only [EntireSimpleSlopes.radius, a, hσ]
  -- the images of the zeros in `𝔽_p((1/T))` are zeros in `L`
  have hσu : ∀ d, EntireSimpleSlopes.eval a (σ (u d)) = 0 := by
    intro d
    have hsum : Summable fun k => γ k * u d ^ k :=
      EntireSimpleSlopes.summable_of_tendsto (hγ.tendsto_norm_term _)
    have := hsum.map_tsum σ (isometry_σ hσ).continuous
    simp only [map_mul, map_pow] at this
    rw [EntireSimpleSlopes.eval, ← this, ← EntireSimpleSlopes.eval, (hu d).2, map_zero]
  have hnormσu : ∀ d, ‖σ (u d)‖ = EntireSimpleSlopes.radius a d := fun d => by
    rw [hσ, (hu d).1, hrad']
  refine ⟨fun x hx => ?_, fun d => ?_⟩
  · rw [gossZeta_eq_eval hσ τ hq]
    constructor
    · intro h0
      obtain ⟨d, hd⟩ := ha.exists_radius_of_eval_eq_zero h0
      refine ⟨d, ?_⟩
      have := ha.eq_of_eval_eq_zero (hnormσu d) (hσu d) hd h0
      rw [map_inv₀, ← this, inv_inv]
    · rintro ⟨d, rfl⟩
      rw [map_inv₀, inv_inv]
      exact hσu d
  · set r := EntireSimpleSlopes.radius γ d
    refine ⟨r ^ d * ‖γ (d + 1)‖ * r ^ 2, by positivity [hrad d, hγ.norm_pos (d + 1)], fun x hx => ?_⟩
    have hx0 : x ≠ 0 := fun h0 => by
      rw [h0, norm_zero, norm_inv, (hu d).1] at hx
      exact (inv_pos.mpr (hrad d)).ne hx
    have hxinv : ‖x⁻¹‖ = EntireSimpleSlopes.radius a d := by
      rw [norm_inv, hx, norm_inv, (hu d).1, inv_inv, hrad']
    rw [gossZeta_eq_eval hσ τ hq, ha.norm_eval_eq (hnormσu d) (hσu d) hxinv, hrad']
    have hσu0 : σ (u d) ≠ 0 := (map_ne_zero σ).mpr (hu0 d)
    have hdiff : x⁻¹ - σ (u d) = (σ (u d)⁻¹ - x) * (x⁻¹ * σ (u d)) := by
      rw [map_inv₀]
      field_simp
    rw [hdiff, norm_mul, norm_mul, norm_inv, hx, norm_inv, (hu d).1, inv_inv, hσ, (hu d).1,
      norm_sub_rev, map_inv₀]
    simp only [γ, r]
    ring

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
