import GaloisForLFunctions.RHTower.LiSignAlongSquares
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Li's criterion along polynomial sequences, and its arithmetic obstruction

Let `P ∈ ℕ[X]` have degree `≥ 1` and no constant term. If the Riemann hypothesis fails, there are
`T ≥ 1` and `c > 0` with `Re 2λ_{P(Tk)} < 0` for at least `cN` of the `k < N`
(`exists_density_re_xiLiPaired_poly_neg_of_not_riemannHypothesis`). Hence the Riemann hypothesis
holds iff `Re 2λ_{P(m)} ≥ 0` for all large `m`
(`riemannHypothesis_iff_eventually_re_xiLiPaired_poly_nonneg`).

**Obstruction.** Along a sequence that avoids the class `0 mod b` the mechanism fails: for the `b − 1`
nontrivial `b`-th roots of unity `ζ^a`, the cosine sum `Σ_a Re(ζ^{an})` equals `−1` whenever
`b ∤ n` (`sum_re_rootOfUnity_pow_eq_neg_one`). An abstract Li family with Cayley roots `Rζ^a`,
`R > 1`, has all paired sums positive along such a sequence (`re_sum_liTerm_rootFamily_pos`). So
some arithmetic recurrence of the index sequence (here `T ∣ P(Tk)`) is necessary.

**Mechanism.**
* *Polynomial Weyl sums.* A phase `g : ℤ → ℤ` with constant nonzero `d`-th difference
  (`ConstDiffPhase d g`) has `Σ_{k<N} w^{g(k)} = o(N)` for unimodular `w` that is not a root of
  unity. The proof inducts on `d`: the case `d = 1` is a geometric sum, and the van der Corput
  inequality turns degree `d + 1` into the differenced phases `g(n+h) − g(n)` of degree `d`.
* *Moments.* The first and second moments along `s(k) = P(Tk)` are those of the squares
  (`exists_card_filter_seq_gt`), because `T ∣ P(Tk)` makes every root of unity of order dividing
  `T` equal to `1` along the sequence.
-/

open Complex Filter Finset Polynomial

noncomputable section

namespace RHTower

/-! ## Phases with constant difference -/

/-- A phase `g : ℤ → ℤ` whose `d`-th unit forward difference is a nonzero constant. -/
def ConstDiffPhase (d : ℕ) (g : ℤ → ℤ) : Prop :=
  ∃ c : ℤ, c ≠ 0 ∧ ∀ n, (fwdDiff 1)^[d] g n = c

theorem fwdDiff_int_comm (h k : ℤ) (f : ℤ → ℤ) :
    fwdDiff h (fwdDiff k f) = fwdDiff k (fwdDiff h f) := by
  funext n
  simp only [fwdDiff, add_right_comm n h k]
  ring

theorem eq_add_mul_of_fwdDiff_one_eq {f : ℤ → ℤ} {c : ℤ} (hf : ∀ n, fwdDiff 1 f n = c) :
    ∀ n, f n = f 0 + c * n := by
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have h1 := hf i
    simp only [fwdDiff] at h1
    linarith
  | pred i ih =>
    have h1 := hf (-(i : ℤ) - 1)
    simp only [fwdDiff, sub_add_cancel] at h1
    linarith

/-- The shifted difference of a phase of order `d + 1` is a phase of order `d`. -/
theorem ConstDiffPhase.fwdDiff_shift {d : ℕ} {g : ℤ → ℤ} (hg : ConstDiffPhase (d + 1) g)
    {h : ℤ} (hh : h ≠ 0) : ConstDiffPhase d (fwdDiff h g) := by
  obtain ⟨c, hc, hgc⟩ := hg
  refine ⟨c * h, mul_ne_zero hc hh, fun n => ?_⟩
  have hcomm : Function.Commute (fwdDiff (1 : ℤ) : (ℤ → ℤ) → (ℤ → ℤ)) (fwdDiff h) :=
    fun F => fwdDiff_int_comm 1 h F
  rw [(hcomm.iterate_left d) g]
  set ℓ : ℤ → ℤ := (fwdDiff 1)^[d] g with hℓ
  have hℓc : ∀ m, fwdDiff 1 ℓ m = c := fun m => by
    have := hgc m
    rwa [Function.iterate_succ_apply'] at this
  have hlin := eq_add_mul_of_fwdDiff_one_eq hℓc
  simp only [fwdDiff]
  rw [hlin (n + h), hlin n]
  ring

/-! ## Polynomial Weyl sums -/

theorem conj_eq_inv_of_unit_norm {z : ℂ} (hz : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  simp

theorem ne_zero_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h0; rw [h0, norm_zero] at hz; exact zero_ne_one hz

theorem zpow_ne_one_of_not_root {w : ℂ} (hroot : ∀ n : ℕ, 0 < n → w ^ n ≠ 1) {c : ℤ}
    (hc : c ≠ 0) : w ^ c ≠ 1 := by
  intro h
  rcases Int.natAbs_eq c with hc' | hc'
  · rw [hc', zpow_natCast] at h; exact hroot _ (Int.natAbs_pos.mpr hc) h
  · rw [hc', zpow_neg, zpow_natCast, inv_eq_one] at h; exact hroot _ (Int.natAbs_pos.mpr hc) h

theorem weylCorr_zpow {w : ℂ} (hw : ‖w‖ = 1) (g : ℤ → ℤ) (N h : ℕ) :
    Sieve.weylCorr (fun k : ℕ => w ^ (g k)) N h =
      ∑ n ∈ range (N - h), w ^ (fwdDiff (h : ℤ) g n) := by
  unfold Sieve.weylCorr
  refine sum_congr rfl fun n _ => ?_
  have hw0 := ne_zero_of_norm_eq_one hw
  have hn : ‖w ^ g n‖ = 1 := by rw [norm_zpow, hw, one_zpow]
  simp only [fwdDiff]
  rw [conj_eq_inv_of_unit_norm hn, ← div_eq_mul_inv, ← zpow_sub₀ hw0]
  push_cast
  rfl

/-- **Polynomial Weyl sums are `o(N)`.** If `g` has constant nonzero `d`-th difference, `d ≥ 1`,
and the unimodular `w` is not a root of unity, then `‖Σ_{k<N} w^{g(k)}‖ ≤ δN` for all large `N`. -/
theorem eventually_norm_sum_zpow_le (d : ℕ) (hd : 1 ≤ d) :
    ∀ {g : ℤ → ℤ}, ConstDiffPhase d g → ∀ {w : ℂ}, ‖w‖ = 1 →
      (∀ n : ℕ, 0 < n → w ^ n ≠ 1) → ∀ {δ : ℝ}, 0 < δ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (g k)‖ ≤ δ * N := by
  induction d, hd using Nat.le_induction with
  | base =>
    intro g hg w hw hroot δ hδ
    obtain ⟨c, hc, hgc⟩ := hg
    have hw0 := ne_zero_of_norm_eq_one hw
    have hlin := eq_add_mul_of_fwdDiff_one_eq (f := g) (c := c) (fun n => by
      have := hgc n; rwa [Function.iterate_one] at this)
    have hwc : w ^ c ≠ 1 := zpow_ne_one_of_not_root hroot hc
    have hwcn : ‖w ^ c‖ = 1 := by rw [norm_zpow, hw, one_zpow]
    set B : ℝ := 2 / ‖w ^ c - 1‖ with hB
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (B / δ)
    refine ⟨N₀, fun N hN => ?_⟩
    have hsum : ∑ k ∈ range N, w ^ (g k) = w ^ (g 0) * ∑ k ∈ range N, (w ^ c) ^ k := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [hlin k, zpow_add₀ hw0, zpow_mul, zpow_natCast]
    rw [hsum, norm_mul, norm_zpow, hw, one_zpow, one_mul]
    have hgeom := norm_geom_sum_le_of_norm_eq_one hwcn hwc N
    have hBN : B ≤ δ * N := by
      have h1 : B / δ < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
      rw [div_lt_iff₀ hδ] at h1; linarith
    linarith
  | succ d hd ih =>
    intro g hg w hw hroot δ hδ
    obtain ⟨H, hH⟩ := exists_nat_gt (8 / δ ^ 2)
    have hHpos : (0 : ℝ) < H := lt_trans (by positivity) hH
    have hH1 : 1 ≤ H := by exact_mod_cast hHpos
    have hδ' : (0 : ℝ) < δ ^ 2 / 8 := by positivity
    have hex : ∀ h : ℕ, ∃ N₀ : ℕ, 1 ≤ h → ∀ M : ℕ, N₀ ≤ M →
        ‖∑ n ∈ range M, w ^ (fwdDiff (h : ℤ) g n)‖ ≤ δ ^ 2 / 8 * M := by
      intro h
      by_cases hh : 1 ≤ h
      · have hh0 : (h : ℤ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
        obtain ⟨N₀, hN₀⟩ := ih (hg.fwdDiff_shift hh0) hw hroot hδ'
        exact ⟨N₀, fun _ => hN₀⟩
      · exact ⟨0, fun h1 => absurd h1 hh⟩
    choose N₁ hN₁ using hex
    set N₂ : ℕ := (Icc 1 (H - 1)).sup (fun h => N₁ h + h) with hN₂
    refine ⟨max H N₂, fun N hN => ?_⟩
    have hHN : H ≤ N := le_trans (le_max_left _ _) hN
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hHpos (by exact_mod_cast hHN)
    have hvdc := Sieve.weyl_vdc (fun k : ℕ => w ^ (g k))
      (fun k => by rw [norm_zpow, hw, one_zpow]) N H hH1 hHN
    have hcorr : ∀ h ∈ Icc 1 (H - 1),
        ‖Sieve.weylCorr (fun k : ℕ => w ^ (g k)) N h‖ ≤ δ ^ 2 / 8 * N := by
      intro h hh
      have hh1 : 1 ≤ h := (mem_Icc.mp hh).1
      have hle : N₁ h + h ≤ N :=
        le_trans (Finset.le_sup (f := fun h => N₁ h + h) hh) (le_trans (le_max_right _ _) hN)
      rw [weylCorr_zpow hw]
      have := hN₁ h hh1 (N - h) (by omega)
      refine le_trans this ?_
      have : ((N - h : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N h
      gcongr
    have hsumcorr : ∑ h ∈ Icc 1 (H - 1), ‖Sieve.weylCorr (fun k : ℕ => w ^ (g k)) N h‖
        ≤ H * (δ ^ 2 / 8 * N) := by
      refine le_trans (sum_le_sum hcorr) ?_
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
      have : ((H - 1 + 1 - 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast (by omega : H - 1 + 1 - 1 ≤ H)
      gcongr
    set S : ℝ := ‖∑ k ∈ range N, w ^ (g k)‖ with hS
    have hS0 : 0 ≤ S := norm_nonneg _
    have h1 : (H : ℝ) * S ^ 2 ≤ 4 * N * (N + H * (δ ^ 2 / 8 * N)) := by
      refine le_trans hvdc ?_
      gcongr
    have hHδ : 8 < (H : ℝ) * δ ^ 2 := by
      rw [div_lt_iff₀ (by positivity)] at hH; linarith
    have h2 : (H : ℝ) * S ^ 2 ≤ (H : ℝ) * (δ * N) ^ 2 := by
      have a1 : 8 * (N : ℝ) ^ 2 ≤ H * δ ^ 2 * N ^ 2 :=
        mul_le_mul_of_nonneg_right hHδ.le (sq_nonneg _)
      nlinarith
    have h3 : S ^ 2 ≤ (δ * N) ^ 2 := le_of_mul_le_mul_left h2 hHpos
    exact (pow_le_pow_iff_left₀ hS0 (by positivity) two_ne_zero).mp h3

/-! ## Cosine sums along divisible index families -/

/-- Along a family with `T ∣ s T k`, the sums of `w^{s T k}` are `N` (if `w^T = 1`) or `o(N)`. -/
theorem eventually_neg_le_re_sum_seq {s : ℕ → ℕ → ℕ} (hdiv : ∀ T k, T ∣ s T k)
    (hweyl : ∀ T : ℕ, 0 < T → ∀ w : ℂ, ‖w‖ = 1 → (∀ n : ℕ, 0 < n → w ^ n ≠ 1) →
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (s T k)‖ ≤ δ * N)
    {w : ℂ} (hw : ‖w‖ = 1) {Q : ℕ} (hQ : 0 < Q)
    (hd : w ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → w ^ n ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → -(δ * N) ≤ (∑ k ∈ range N, w ^ (s Q k)).re := by
  rcases hd with h1 | hnr
  · refine ⟨0, fun N _ => ?_⟩
    have hk : ∀ k : ℕ, w ^ (s Q k) = 1 := fun k => by
      obtain ⟨j, hj⟩ := hdiv Q k
      rw [hj, pow_mul, h1, one_pow]
    simp only [hk, sum_const, card_range, nsmul_eq_mul, mul_one, natCast_re]
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    nlinarith
  · obtain ⟨N₀, hN₀⟩ := hweyl Q hQ w hw hnr δ hδ
    refine ⟨N₀, fun N hN => ?_⟩
    have h1 := hN₀ N hN
    have h2 := Complex.abs_re_le_norm (∑ k ∈ range N, w ^ (s Q k))
    have h3 := neg_abs_le (∑ k ∈ range N, w ^ (s Q k)).re
    linarith

/-- **Positive density along a divisible index family.** If `T ∣ s T k` and the sums
`Σ_{k<N} w^{s T k}` are `o(N)` off the roots of unity, then for unimodular `u_i` and `m_i > 0` there
are `Q ≥ 1` and `ε, c > 0` with `Σ_i m_i Re(u_i^{s Q k}) > ε` for at least `cN` of the `k < N`. -/
theorem exists_card_filter_seq_gt {ι : Type*} [Fintype ι] [Nonempty ι] (idx : ℕ → ℕ → ℕ)
    (hdiv : ∀ T k, T ∣ idx T k)
    (hweyl : ∀ T : ℕ, 0 < T → ∀ w : ℂ, ‖w‖ = 1 → (∀ n : ℕ, 0 < n → w ^ n ≠ 1) →
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (idx T k)‖ ≤ δ * N)
    (u : ι → ℂ) (m : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1) (hm : ∀ i, 0 < m i) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((range N).filter
        (fun k => ε < ∑ i, m i * (u i ^ (idx Q k)).re)).card : ℝ) := by
  classical
  obtain ⟨Q₁, hQ₁, hd₁⟩ := exists_pow_eq_one_or_not_root u
  obtain ⟨Q₂, hQ₂, hd₂⟩ := exists_pow_eq_one_or_not_root (fun p : ι × ι => u p.1 * u p.2)
  obtain ⟨Q₃, hQ₃, hd₃⟩ :=
    exists_pow_eq_one_or_not_root (fun p : ι × ι => u p.1 * (starRingEnd ℂ) (u p.2))
  set Q : ℕ := Q₁ * Q₂ * Q₃ with hQ
  have hQpos : 0 < Q := Nat.mul_pos (Nat.mul_pos hQ₁ hQ₂) hQ₃
  have e₁ : ∀ i, u i ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → u i ^ n ≠ 1 := fun i =>
    pow_eq_one_or_not_root_of_dvd (hd₁ i) ⟨Q₂ * Q₃, by rw [hQ]; ring⟩
  have e₂ : ∀ p : ι × ι, (u p.1 * u p.2) ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → (u p.1 * u p.2) ^ n ≠ 1 :=
    fun p => pow_eq_one_or_not_root_of_dvd (hd₂ p) ⟨Q₁ * Q₃, by rw [hQ]; ring⟩
  have e₃ : ∀ p : ι × ι, (u p.1 * (starRingEnd ℂ) (u p.2)) ^ Q = 1 ∨
      ∀ n : ℕ, 0 < n → (u p.1 * (starRingEnd ℂ) (u p.2)) ^ n ≠ 1 :=
    fun p => pow_eq_one_or_not_root_of_dvd (hd₃ p) ⟨Q₁ * Q₂, by rw [hQ]; ring⟩
  have hu₂ : ∀ p : ι × ι, ‖u p.1 * u p.2‖ = 1 := fun p => by
    rw [norm_mul, hu, hu, one_mul]
  have hu₃ : ∀ p : ι × ι, ‖u p.1 * (starRingEnd ℂ) (u p.2)‖ = 1 := fun p => by
    rw [norm_mul, Complex.norm_conj, hu, hu, one_mul]
  set f : ℕ → ℝ := fun k => ∑ i, m i * (u i ^ (idx Q k)).re with hf
  set B : ℝ := ∑ i, m i with hBdef
  have hB0 : 0 < B := Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  have hfB : ∀ k, |f k| ≤ B := by
    intro k
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hm i)]
    have h1 := Complex.abs_re_le_norm (u i ^ (idx Q k))
    rw [norm_pow, hu, one_pow] at h1
    nlinarith [hm i]
  set s : ℝ := (∑ i, m i ^ 2) / 2 with hsdef
  have hs0 : 0 < s := by
    have : 0 < ∑ i, m i ^ 2 := Finset.sum_pos (fun i _ => by have := hm i; positivity)
      Finset.univ_nonempty
    positivity
  have hmean : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → -(δ * N) ≤ ∑ k ∈ range N, f k := by
    intro δ hδ
    have hex : ∀ i, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ / B * N) ≤ (∑ k ∈ range N, u i ^ (idx Q k)).re := fun i =>
      eventually_neg_le_re_sum_seq hdiv hweyl (hu i) hQpos (e₁ i) (by positivity)
    choose N₀ hN₀ using hex
    refine ⟨Finset.univ.sup N₀, fun N hN => ?_⟩
    have hswap : ∑ k ∈ range N, f k = ∑ i, m i * (∑ k ∈ range N, u i ^ (idx Q k)).re := by
      simp only [hf]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_sum, Finset.mul_sum]
    rw [hswap]
    have hle : ∀ i ∈ (Finset.univ : Finset ι),
        m i * (-(δ / B * N)) ≤ m i * (∑ k ∈ range N, u i ^ (idx Q k)).re := fun i _ =>
      mul_le_mul_of_nonneg_left
        (hN₀ i N (le_trans (Finset.le_sup (Finset.mem_univ i)) hN)) (hm i).le
    have hsum := Finset.sum_le_sum hle
    have heq : ∑ i, m i * (-(δ / B * N)) = -(δ * N) := by
      rw [← Finset.sum_mul, ← hBdef]; field_simp
    linarith
  have hsq : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (s - δ) * N ≤ ∑ k ∈ range N, f k ^ 2 := by
    intro δ hδ
    set δ' : ℝ := δ / (B ^ 2 + 1) with hδ'
    have hδ'0 : 0 < δ' := by positivity
    have hex₂ : ∀ p : ι × ι, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ' * N) ≤ (∑ k ∈ range N, (u p.1 * u p.2) ^ (idx Q k)).re := fun p =>
      eventually_neg_le_re_sum_seq hdiv hweyl (hu₂ p) hQpos (e₂ p) hδ'0
    have hex₃ : ∀ p : ι × ι, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ' * N) ≤ (∑ k ∈ range N, (u p.1 * (starRingEnd ℂ) (u p.2)) ^ (idx Q k)).re :=
      fun p => eventually_neg_le_re_sum_seq hdiv hweyl (hu₃ p) hQpos (e₃ p) hδ'0
    choose N₂ hN₂ using hex₂
    choose N₃ hN₃ using hex₃
    refine ⟨max (Finset.univ.sup N₂) (Finset.univ.sup N₃), fun N hN => ?_⟩
    have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
    -- the double-sum form of the second moment
    have hswap : ∑ k ∈ range N, f k ^ 2 = ∑ i, ∑ j, m i * m j / 2 *
        ((∑ k ∈ range N, (u i * u j) ^ (idx Q k)).re +
          (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (idx Q k)).re) := by
      simp only [hf, sq_sum_mul_re_pow_eq]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    rw [hswap]
    -- each pair is at least `[i = j]N − 2δ'N`
    have hpair : ∀ i j, (if i = j then (N : ℝ) else 0) - 2 * δ' * N ≤
        (∑ k ∈ range N, (u i * u j) ^ (idx Q k)).re +
          (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (idx Q k)).re := by
      intro i j
      have h2 := hN₂ (i, j) N (le_trans (Finset.le_sup (Finset.mem_univ (i, j)))
        (le_trans (le_max_left _ _) hN))
      have h3 := hN₃ (i, j) N (le_trans (Finset.le_sup (Finset.mem_univ (i, j)))
        (le_trans (le_max_right _ _) hN))
      simp only at h2 h3
      have hδN : 0 ≤ δ' * N := mul_nonneg hδ'0.le hN0
      split_ifs with hij
      · subst hij
        have hone : u i * (starRingEnd ℂ) (u i) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
        rw [hone]
        simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, natCast_re]
        linarith
      · linarith
    have hlow : ∑ i, ∑ j, m i * m j / 2 * ((if i = j then (N : ℝ) else 0) - 2 * δ' * N) ≤
        ∑ i, ∑ j, m i * m j / 2 *
          ((∑ k ∈ range N, (u i * u j) ^ (idx Q k)).re +
            (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (idx Q k)).re) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hpair i j) (by have := hm i; have := hm j; positivity)
    have heval : ∑ i, ∑ j, m i * m j / 2 * ((if i = j then (N : ℝ) else 0) - 2 * δ' * N) =
        s * N - δ' * B ^ 2 * N := by
      have h1 : ∀ i, ∑ j, m i * m j / 2 * ((if i = j then (N : ℝ) else 0) - 2 * δ' * N) =
          m i ^ 2 / 2 * N - m i * B * δ' * N := by
        intro i
        simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
        rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum, ← hBdef]
        ring
      have e1 : ∑ i, m i ^ 2 / 2 * (N : ℝ) = s * N := by
        rw [hsdef, Finset.sum_div, Finset.sum_mul]
      have e2 : ∑ i, m i * B * δ' * (N : ℝ) = δ' * B ^ 2 * N := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← hBdef]; ring
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, e1, e2]
    have hδB : δ' * B ^ 2 ≤ δ := by
      rw [hδ', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    rw [heval] at hlow
    nlinarith
  obtain ⟨ε, c, hε, hc, N₀, hcount⟩ := exists_card_filter_gt_of_mean_sq hB0 hfB hs0 hmean hsq
  exact ⟨Q, hQpos, ε, c, hε, hc, N₀, hcount⟩

/-! ## Polynomial index families -/

theorem dvd_eval_mul_of_coeff_zero {P : ℕ[X]} (hP0 : P.coeff 0 = 0) (T k : ℕ) :
    T ∣ P.eval (T * k) := by
  obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_iff.mpr hP0
  rw [hQ, eval_mul, eval_X, mul_assoc]
  exact dvd_mul_right _ _

theorem le_eval_mul_of_natDegree_pos {P : ℕ[X]} (hPd : 1 ≤ P.natDegree) {T : ℕ} (hT : 0 < T)
    (k : ℕ) : k ≤ P.eval (T * k) := by
  have hP : P ≠ 0 := by rintro rfl; simp at hPd
  have hlead : 1 ≤ P.leadingCoeff := Nat.one_le_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
  rw [eval_eq_sum_range]
  have hterm : P.coeff P.natDegree * (T * k) ^ P.natDegree ≤
      ∑ i ∈ range (P.natDegree + 1), P.coeff i * (T * k) ^ i :=
    Finset.single_le_sum (f := fun i => P.coeff i * (T * k) ^ i) (fun _ _ => Nat.zero_le _)
      (mem_range.mpr (Nat.lt_succ_self _))
  rw [coeff_natDegree] at hterm
  have h1 : k ≤ T * k := Nat.le_mul_of_pos_left k hT
  have h2 : T * k ≤ (T * k) ^ P.natDegree := Nat.le_self_pow (by omega) _
  have h3 : (T * k) ^ P.natDegree ≤ P.leadingCoeff * (T * k) ^ P.natDegree :=
    Nat.le_mul_of_pos_left _ hlead
  omega

/-- The phase `x ↦ P(Tx)` has constant nonzero `deg P`-th difference. -/
theorem polySeq_constDiffPhase {P : ℕ[X]} (hPd : 1 ≤ P.natDegree) {T : ℕ} (hT : 0 < T) :
    ConstDiffPhase P.natDegree
      (fun x : ℤ => ((P.map (Nat.castRingHom ℤ)).comp (C (T : ℤ) * X)).eval x) := by
  set Q : ℤ[X] := (P.map (Nat.castRingHom ℤ)).comp (C (T : ℤ) * X) with hQ
  have hT0 : (T : ℤ) ≠ 0 := by exact_mod_cast hT.ne'
  have hlin : (C (T : ℤ) * X).natDegree = 1 := natDegree_C_mul_X _ hT0
  have hinj : Function.Injective (Nat.castRingHom ℤ) := Nat.cast_injective
  have hdeg : Q.natDegree = P.natDegree := by
    rw [hQ, natDegree_comp, hlin, mul_one, natDegree_map_eq_of_injective hinj]
  have hP : P ≠ 0 := by rintro rfl; simp at hPd
  have hlc : Q.leadingCoeff ≠ 0 := by
    rw [hQ, leadingCoeff_comp (by rw [hlin]; norm_num), leadingCoeff_map_of_injective hinj]
    have h1 : (C (T : ℤ) * X).leadingCoeff = (T : ℤ) := leadingCoeff_C_mul_X _
    rw [h1]
    exact mul_ne_zero (by simpa using leadingCoeff_ne_zero.mpr hP) (pow_ne_zero _ hT0)
  refine ⟨Q.leadingCoeff * (P.natDegree.factorial : ℤ),
    mul_ne_zero hlc (by exact_mod_cast (Nat.factorial_pos _).ne'), fun n => ?_⟩
  have := congrFun (fwdDiff_iter_degree_eq_factorial Q) n
  rw [hdeg] at this
  rw [this, Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]

/-- Weyl sums along `P(Tk)` are `o(N)` off the roots of unity. -/
theorem polySeq_weyl {P : ℕ[X]} (hPd : 1 ≤ P.natDegree) (T : ℕ) (hT : 0 < T) (w : ℂ)
    (hw : ‖w‖ = 1) (hroot : ∀ n : ℕ, 0 < n → w ^ n ≠ 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (P.eval (T * k))‖ ≤ δ * N := by
  obtain ⟨N₀, hN₀⟩ := eventually_norm_sum_zpow_le P.natDegree hPd
    (polySeq_constDiffPhase hPd hT) hw hroot hδ
  refine ⟨N₀, fun N hN => ?_⟩
  have e : ∀ k : ℕ, w ^ (((P.map (Nat.castRingHom ℤ)).comp (C (T : ℤ) * X)).eval (k : ℤ)) =
      w ^ (P.eval (T * k)) := by
    intro k
    have h1 : (C (T : ℤ) * X).eval (k : ℤ) = ((T * k : ℕ) : ℤ) := by simp
    rw [eval_comp, h1, eval_natCast_map, ← zpow_natCast]
    simp
  have := hN₀ N hN
  rwa [Finset.sum_congr rfl fun k _ => e k] at this

/-! ## Li coefficients along polynomial sequences -/

/-- **Negative along `P(Tk)` with positive density, abstract form.** -/
theorem exists_density_poly_re_tsum_liTerm_neg {P : ℕ[X]} (hP0 : P.coeff 0 = 0)
    (hPd : 1 ≤ P.natDegree) {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ T : ℕ, 0 < T ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((range N).filter
        (fun k => ∑' i, m i * (liTerm (v i) (P.eval (T * k))).re < 0)).card : ℝ) := by
  classical
  obtain ⟨D, R, hDne, hR1, hDnorm, hdec⟩ := abs_re_tsum_liTerm_add_dominant_le hm hv hM hs hlt
  have hR0 : (0 : ℝ) < R := by linarith
  haveI : Nonempty {x // x ∈ D} := ⟨⟨hDne.choose, hDne.choose_spec⟩⟩
  set u : {x // x ∈ D} → ℂ := fun i => v i / R with hudef
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hudef]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, (hDnorm i).mp i.2,
      div_self hR0.ne']
  obtain ⟨T, hT, ε, c, hε, hc, N₀, hcount⟩ :=
    exists_card_filter_seq_gt (fun T k => P.eval (T * k)) (dvd_eval_mul_of_coeff_zero hP0)
      (fun T hT w hw hroot δ hδ => polySeq_weyl hPd T hT w hw hroot δ hδ)
      u (fun i => m i) hunit (fun i => by linarith [hm i])
  obtain ⟨N₁, hN₁⟩ := hdec (ε / 2) (by linarith)
  have hf : ∀ n, ∑ i : {x // x ∈ D}, m i * (u i ^ n).re = ∑ i ∈ D, m i * ((v i / R) ^ n).re :=
    fun n => Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n).re)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * N₁ / c)
  refine ⟨T, hT, c / 2, by positivity, max N₀ N₂, fun N hN => ?_⟩
  have hle := card_filter_le_card_filter_add
    (P := fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (P.eval (T * k))).re)
    (Q := fun k => ∑' i, m i * (liTerm (v i) (P.eval (T * k))).re < 0) (N₁ := N₁)
    (fun k hk hP => by
      have hn : N₁ ≤ P.eval (T * k) := le_trans hk (le_eval_mul_of_natDegree_pos hPd hT k)
      have hd := hN₁ _ hn
      rw [hf] at hP
      have hRn : (0 : ℝ) < R ^ (P.eval (T * k)) := pow_pos hR0 _
      have h2 := (abs_le.mp hd).2
      have h3 := mul_pos hRn (sub_pos.mpr hP)
      nlinarith) N
  have h1 := hcount N (le_trans (le_max_left _ _) hN)
  have hle' : (((range N).filter
      (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (P.eval (T * k))).re)).card : ℝ)
      ≤ (((range N).filter
        (fun k => ∑' i, m i * (liTerm (v i) (P.eval (T * k))).re < 0)).card : ℝ) + N₁ := by
    exact_mod_cast hle
  have hNN : 2 * N₁ / c < N :=
    lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right _ _) hN)
  rw [div_lt_iff₀ hc] at hNN
  linarith

/-- **Off the critical line the Li coefficients are negative along `P(Tk)` with positive
density.** -/
theorem exists_density_re_xiLiPaired_poly_neg_of_not_riemannHypothesis {P : ℕ[X]}
    (hP0 : P.coeff 0 = 0) (hPd : 1 ≤ P.natDegree) (hRH : ¬ RiemannHypothesis) :
    ∃ T : ℕ, 0 < T ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((range N).filter (fun k => (xiLiPaired (P.eval (T * k))).re < 0)).card : ℝ) := by
  classical
  obtain ⟨M, hmult, hvnorm, hvM, hsum, _, hbad⟩ := xiLi_family_facts
  obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
  obtain ⟨T, hT, c, hc, N₀, hcount⟩ :=
    exists_density_poly_re_tsum_liTerm_neg hP0 hPd hmult hvnorm hvM hsum hρ₀
  refine ⟨T, hT, c, hc, N₀, fun N hN => ?_⟩
  simp_rw [re_xiLiPaired_eq_tsum_mult]
  exact hcount N hN

/-- **Li's criterion along a polynomial sequence.** For `P ∈ ℕ[X]` of degree `≥ 1` without constant
term, the Riemann hypothesis holds iff `Re 2λ_{P(m)} ≥ 0` for all large `m`. -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_poly_nonneg {P : ℕ[X]}
    (hP0 : P.coeff 0 = 0) (hPd : 1 ≤ P.natDegree) :
    RiemannHypothesis ↔ ∀ᶠ m in atTop, 0 ≤ (xiLiPaired (P.eval m)).re := by
  classical
  constructor
  · intro hRH
    exact Filter.Eventually.of_forall fun m => re_xiLiPaired_nonneg_of_rh hRH _
  · intro h
    by_contra hRH
    obtain ⟨T, hT, c, hc, N₀, hcount⟩ :=
      exists_density_re_xiLiPaired_poly_neg_of_not_riemannHypothesis hP0 hPd hRH
    obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp h
    obtain ⟨N, hN⟩ := exists_nat_gt ((M₀ : ℝ) / c + N₀)
    have hM0 : (0 : ℝ) ≤ (M₀ : ℝ) / c := by positivity
    have hNN₀ : N₀ ≤ N := by
      have : (N₀ : ℝ) < N := by linarith
      exact_mod_cast this.le
    have h1 := hcount N hNN₀
    have hcN : (M₀ : ℝ) < c * N := by
      have : (M₀ : ℝ) / c < N := by linarith
      rwa [div_lt_iff₀ hc, mul_comm] at this
    have hbig : M₀ < ((range N).filter (fun k => (xiLiPaired (P.eval (T * k))).re < 0)).card := by
      have : (M₀ : ℝ) < (((range N).filter
          (fun k => (xiLiPaired (P.eval (T * k))).re < 0)).card : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨k, hk, hkM⟩ : ∃ k ∈ (range N).filter (fun k => (xiLiPaired (P.eval (T * k))).re < 0),
        M₀ ≤ k := by
      by_contra hno
      push Not at hno
      have hsub : (range N).filter (fun k => (xiLiPaired (P.eval (T * k))).re < 0) ⊆ range M₀ :=
        fun k hk => mem_range.mpr (hno k hk)
      have := card_le_card hsub
      rw [card_range] at this
      omega
    have hneg := (mem_filter.mp hk).2
    have hnn := hM₀ (T * k) (le_trans hkM (Nat.le_mul_of_pos_left k hT))
    linarith

/-! ## The arithmetic obstruction -/

/-- The primitive root of unity `e^{2πi/b}`. -/
def primitiveRootExp (b : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / b)

/-- **Ramanujan sums.** For `b ≥ 2` and `b ∤ n`, `Σ_{a=1}^{b−1} (ζ^a)ⁿ = −1`, `ζ = e^{2πi/b}`. -/
theorem sum_primitiveRootExp_pow_eq_neg_one {b n : ℕ} (hb : 2 ≤ b) (hn : ¬ b ∣ n) :
    ∑ a ∈ Ico 1 b, (primitiveRootExp b ^ a) ^ n = -1 := by
  have hprim : IsPrimitiveRoot (primitiveRootExp b) b :=
    Complex.isPrimitiveRoot_exp b (by omega)
  set x : ℂ := primitiveRootExp b ^ n with hx
  have hx1 : x ≠ 1 := fun h => hn ((hprim.pow_eq_one_iff_dvd n).mp h)
  have hxb : x ^ b = 1 := by rw [hx, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hgeom : ∑ a ∈ range b, x ^ a = 0 := by
    rw [geom_sum_eq hx1, hxb, sub_self, zero_div]
  have hterm : ∀ a, (primitiveRootExp b ^ a) ^ n = x ^ a := fun a => by
    rw [hx, ← pow_mul, ← pow_mul, mul_comm]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at hgeom
  simp only [pow_zero, zero_add] at hgeom
  rw [Finset.sum_congr rfl fun a _ => hterm a]
  linear_combination hgeom

/-- **An abstract Li family that the sequence cannot see.** With Cayley roots `Rζ^a`
(`a = 1, …, b−1`, `R > 0`), every paired Li sum at an index `n` with `b ∤ n` is positive:
`Σ_a Re(2 − (Rζ^a)ⁿ − (Rζ^a)⁻ⁿ) = 2(b−1) + Rⁿ + R⁻ⁿ`. -/
theorem re_sum_liTerm_rootFamily_eq {b n : ℕ} (hb : 2 ≤ b) (hn : ¬ b ∣ n) {R : ℝ} (hR : 0 < R) :
    ∑ a ∈ Ico 1 b, (liTerm ((R : ℂ) * primitiveRootExp b ^ a) n).re =
      2 * (b - 1) + R ^ n + (R⁻¹) ^ n := by
  have hprim : IsPrimitiveRoot (primitiveRootExp b) b :=
    Complex.isPrimitiveRoot_exp b (by omega)
  have hnorm : ‖primitiveRootExp b‖ = 1 := hprim.norm'_eq_one (by omega)
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hsum := sum_primitiveRootExp_pow_eq_neg_one hb hn
  have hterm : ∀ a, (liTerm ((R : ℂ) * primitiveRootExp b ^ a) n).re =
      2 - (R ^ n + (R⁻¹) ^ n) * ((primitiveRootExp b ^ a) ^ n).re := by
    intro a
    have hza : ‖primitiveRootExp b ^ a‖ = 1 := by rw [norm_pow, hnorm, one_pow]
    have hinv : (primitiveRootExp b ^ a)⁻¹ = (starRingEnd ℂ) (primitiveRootExp b ^ a) :=
      (conj_eq_inv_of_unit_norm hza).symm
    unfold liTerm
    rw [mul_inv, hinv, mul_pow, mul_pow, ← map_pow]
    simp only [Complex.sub_re, Complex.re_ofNat]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul, Complex.conj_re]
    ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul, ← Finset.mul_sum, ← Complex.re_sum, hsum]
  simp only [Complex.neg_re, Complex.one_re]
  have : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [this]
  ring

theorem re_sum_liTerm_rootFamily_pos {b n : ℕ} (hb : 2 ≤ b) (hn : ¬ b ∣ n) {R : ℝ} (hR : 0 < R) :
    0 < ∑ a ∈ Ico 1 b, (liTerm ((R : ℂ) * primitiveRootExp b ^ a) n).re := by
  rw [re_sum_liTerm_rootFamily_eq hb hn hR]
  have : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 : 0 < R ^ n := pow_pos hR n
  have h2 : 0 < (R⁻¹) ^ n := pow_pos (inv_pos.mpr hR) n
  linarith

/-- **The primes are not a thinning sequence for this mechanism.** The Cayley family `Rζ₄^a`
(`a = 1, 2, 3`) has positive paired Li sums at every prime index, because `4` divides no prime. -/
theorem re_sum_liTerm_rootFamily_four_pos_of_prime {p : ℕ} (hp : p.Prime) {R : ℝ} (hR : 0 < R) :
    0 < ∑ a ∈ Ico 1 4, (liTerm ((R : ℂ) * primitiveRootExp 4 ^ a) p).re := by
  refine re_sum_liTerm_rootFamily_pos (by norm_num) (fun h => ?_) hR
  rcases hp.eq_one_or_self_of_dvd 4 h with h1 | h1
  · norm_num at h1
  · rw [← h1] at hp; norm_num at hp

end RHTower

end
