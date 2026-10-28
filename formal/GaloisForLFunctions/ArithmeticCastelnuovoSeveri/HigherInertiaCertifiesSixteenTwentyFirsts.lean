import GaloisForLFunctions.RHTower.RankTraceBoundAfterRemovingABlock
import GaloisForLFunctions.RHTower.RiemannGaussian.EtaEnergyFiniteWindowInertia
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import GaloisForLFunctions.HTGeometry.MatrixRankSubadditive

/-!
# Higher inertia certifies `16/21` of the zeros at the sine-kernel moments

The zero-side Gram matrix of the census is `Ĥ = A₀ − B`: `A₀ = Σ_{j ∈ S} w_j w_j* + Σ_{j ∈ R} w_j w_j*`
collects one rank-one term per simple critical zero (`j ∈ S`) and one per non-simple block
(`j ∈ R`: a multiple critical zero, column `√m v`, or the positive part of an off-line pair), and
`B ⪰ 0` collects the negative parts of the off-line pairs. The normalization of the non-simple
blocks is the aggregate inequality `Σ_{j∈R} ‖w_j‖² − tr B ≥ 2|R|`: a multiple zero has
`m‖v‖² ≥ 2`, an off-line pair has trace `2`. Simple zeros need no normalization.

* **Certificate class** (`IsInertiaCertificate`): weights `q` with `q ≤ 1`, `q ≤ 0` on `(−∞, 0]`
  and `q(x) ≤ β(2 − x)` for some `β ≥ 0`.
* **Validity** (`sum_le_card_of_isInertiaCertificate`): for every such configuration and every
  weight of the class, `Σ_i q(μ_i(Ĥ)) ≤ |S|`. The eigenvalues `μ_i > 0` number at most `|S| + |R|`
  (`posIndex_sub_le_rank`), the top `|R|` of them sum to at least `2|R|` (Ky Fan,
  `re_trace_mul_projection_le`, on a projection fixing the non-simple columns), and the bound
  splits over the top `|R|`, the next `|S|` and the nonpositive eigenvalues
  (`sum_le_of_isInertiaCertificate`). The rank–trace weight `2x − x²` of the `2/3` theorem is in
  the class (`isInertiaCertificate_rankTrace`).
* **The quartic weight** `q⋆(x) = 1 − (64/49)((x − 1)² − 1/8)²` is in the class with `β = 32/7`
  (`isInertiaCertificate_qStar`). In moments (`sum_qStar_eq_moments`),
  `Σ q⋆(μ_i) = (64/49)(−tr Ĥ⁴ + 4 tr Ĥ³ − (23/4) tr Ĥ² + (7/2) tr Ĥ)`.
* **The number** (`qStar_value_sineMoments`): at the normalized moments `(1, 4/3, 2, 13/4)` of the
  bandwidth-one sine-kernel Gram matrix the certificate equals `16/21 > 3/4`. The fourth moment
  separates the coalescence blind spot: the extremal diagonal `diag(1^{4k}, 2^{k})` of the `2/3`
  theorem has the same first three moments and fourth moment `10/3 ≠ 13/4`
  (`extremalDiag_moments`).
* **Optimality** (`le_sixteen_twentyFirsts_of_valid`): the configuration with sixteen simple pairs of
  eigenvalues `1 ± √2/4` and five coalesced pairs of eigenvalue `2` lies in the model, has exactly
  the sine-kernel moments with `|S| = 32` of `N = 42` zeros, and is attained by `q⋆`. So every
  degree-four polynomial weight valid on the model certifies at most `16/21` at these moments:
  `16/21` is the exact value of fourth-order inertia.
-/

open Matrix Finset
open scoped ComplexOrder
open RiemannGaussian.HermitianRankTrace RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HigherInertia

/-! ### The certificate class -/

/-- Admissible inertia weights: `q ≤ 1`, `q ≤ 0` on `(−∞, 0]`, and `q(x) ≤ β(2 − x)`. -/
def IsInertiaCertificate (q : ℝ → ℝ) : Prop :=
  (∀ x, q x ≤ 1) ∧ (∀ x, x ≤ 0 → q x ≤ 0) ∧ ∃ β : ℝ, 0 ≤ β ∧ ∀ x, q x ≤ β * (2 - x)

/-- **The certificate on a spectrum.** If the eigenvalues beyond the first `s + r` are nonpositive
and the first `r` sum to at least `2r`, every admissible weight sums to at most `s`. -/
theorem sum_le_of_isInertiaCertificate {m : ℕ} (μ : Fin m → ℝ) {s r : ℕ}
    (hpos : ∀ i : Fin m, s + r ≤ (i : ℕ) → μ i ≤ 0)
    (htop : (2 * r : ℝ) ≤ ∑ i ∈ univ.filter (fun i : Fin m => (i : ℕ) < r), μ i)
    {q : ℝ → ℝ} (hq : IsInertiaCertificate q) :
    ∑ i, q (μ i) ≤ s := by
  obtain ⟨h1, h0, β, hβ, hlin⟩ := hq
  set T := univ.filter (fun i : Fin m => (i : ℕ) < r)
  set M := univ.filter (fun i : Fin m => r ≤ (i : ℕ) ∧ (i : ℕ) < s + r)
  set L := univ.filter (fun i : Fin m => s + r ≤ (i : ℕ))
  have hcardT : (T.card : ℝ) ≤ r := by
    have : T.card ≤ r := by
      calc T.card ≤ (Finset.range r).card :=
            Finset.card_le_card_of_injOn (fun i => (i : ℕ))
              (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2)
              (fun i _ j _ h => Fin.ext h)
        _ = r := Finset.card_range r
    exact_mod_cast this
  have hcardM : (M.card : ℝ) ≤ s := by
    have : M.card ≤ s := by
      calc M.card ≤ (Finset.Ico r (s + r)).card :=
            Finset.card_le_card_of_injOn (fun i => (i : ℕ))
              (fun i hi => Finset.mem_Ico.mpr (Finset.mem_filter.mp hi).2)
              (fun i _ j _ h => Fin.ext h)
        _ = s := by rw [Nat.card_Ico]; omega
    exact_mod_cast this
  have hsplit : ∑ i, q (μ i) = ∑ i ∈ T, q (μ i) + ∑ i ∈ M, q (μ i) + ∑ i ∈ L, q (μ i) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i : Fin m => (i : ℕ) < r)]
    rw [add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter fun i : Fin m => ¬ (i : ℕ) < r)
      (fun i : Fin m => (i : ℕ) < s + r), Finset.filter_filter, Finset.filter_filter]
    congr 1
    · refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨not_lt.mp h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨not_lt.mpr h1, h2⟩
    · refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
      constructor
      · rintro ⟨-, h2⟩; exact not_lt.mp h2
      · intro h; exact ⟨by omega, not_lt.mpr h⟩
  have hT : ∑ i ∈ T, q (μ i) ≤ 0 := by
    calc ∑ i ∈ T, q (μ i) ≤ ∑ i ∈ T, β * (2 - μ i) := Finset.sum_le_sum fun i _ => hlin _
      _ = β * (2 * T.card - ∑ i ∈ T, μ i) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ (by linarith)
  have hM : ∑ i ∈ M, q (μ i) ≤ s := by
    calc ∑ i ∈ M, q (μ i) ≤ ∑ _i ∈ M, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 _
      _ = M.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ s := hcardM
  have hL : ∑ i ∈ L, q (μ i) ≤ 0 :=
    Finset.sum_nonpos fun i hi => h0 _ (hpos i (Finset.mem_filter.mp hi).2)
  rw [hsplit]
  linarith

/-! ### The matrix model -/

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem re_trace_nonneg_of_posSemidef {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    0 ≤ (M.trace).re := by
  rw [hM.isHermitian.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hM.eigenvalues_nonneg i

/-- Against an orthogonal projection, a positive semidefinite matrix has trace between `0` and its
own trace. -/
theorem re_trace_mul_projection_mem {M E : Matrix n n ℂ} (hM : M.PosSemidef) (hE : E.IsHermitian)
    (hEE : E * E = E) :
    0 ≤ ((M * E).trace).re ∧ ((M * E).trace).re ≤ (M.trace).re := by
  have hcomp : ∀ F : Matrix n n ℂ, F.IsHermitian → F * F = F →
      (M * F).trace = (Fᴴ * M * F).trace := fun F hF hFF => by
    rw [hF.eq]
    calc (M * F).trace = (M * F * F).trace := by rw [mul_assoc, hFF]
      _ = (F * (M * F)).trace := trace_mul_comm _ _
      _ = (F * M * F).trace := by rw [mul_assoc]
  have h1 := re_trace_nonneg_of_posSemidef (hM.conjTranspose_mul_mul_same E)
  set F : Matrix n n ℂ := 1 - E
  have hF : F.IsHermitian := by
    rw [IsHermitian, conjTranspose_sub, conjTranspose_one, hE.eq]
  have hFF : F * F = F := by
    simp only [F, sub_mul, mul_sub, hEE, one_mul, mul_one]; abel
  have h2 := re_trace_nonneg_of_posSemidef (hM.conjTranspose_mul_mul_same F)
  rw [← hcomp E hE hEE] at h1
  rw [← hcomp F hF hFF] at h2
  refine ⟨h1, ?_⟩
  have : (M * F).trace = M.trace - (M * E).trace := by
    simp only [F, mul_sub, mul_one, trace_sub]
  rw [this, Complex.sub_re] at h2
  linarith

/-- **The certificate on the zero-side model.** Let `Ĥ = A₀ − B` with `A₀, B ⪰ 0`,
`rank A₀ ≤ s + r`, and `A₀ ⪰ G ⪰ 0` with `rank G ≤ r` and `tr G − tr B ≥ 2r`. Then every admissible
weight sums over the spectrum of `Ĥ` to at most `s`. -/
theorem sum_eigenvalues₀_le_of_isInertiaCertificate {H A₀ B G : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA₀ : A₀.PosSemidef) (hB : B.PosSemidef) (hG : G.PosSemidef)
    (hA₀G : (A₀ - G).PosSemidef) (hHAB : H = A₀ - B) {s r : ℕ} (hrank : A₀.rank ≤ s + r)
    (hGrank : G.rank ≤ r) (htr : (2 * r : ℝ) ≤ (G.trace).re - (B.trace).re)
    {q : ℝ → ℝ} (hq : IsInertiaCertificate q) :
    ∑ i, q (hH.eigenvalues₀ i) ≤ s := by
  -- at most `s + r` positive eigenvalues
  have hposcount : #{k | 0 < hH.eigenvalues₀ k} ≤ s + r := by
    have h := RiemannGaussian.HermitianInertia.posIndex_sub_le_rank hA₀ hB
    have hpi : RiemannGaussian.HermitianInertia.posIndex (hA₀.isHermitian.sub hB.isHermitian) =
        RiemannGaussian.HermitianInertia.posIndex hH := by
      subst hHAB; rfl
    rw [hpi, RiemannGaussian.HermitianInertia.posIndex,
      card_eigenvalues_reindex hH (fun x => 0 < x)] at h
    exact h.trans hrank
  have hpos : ∀ i : Fin (Fintype.card n), s + r ≤ (i : ℕ) → hH.eigenvalues₀ i ≤ 0 := by
    intro i hi
    by_contra hneg
    push Not at hneg
    have hsub : (univ.filter fun k : Fin (Fintype.card n) => (k : ℕ) ≤ i) ⊆
        univ.filter fun k => 0 < hH.eigenvalues₀ k := by
      intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk ⊢
      exact lt_of_lt_of_le hneg (hH.eigenvalues₀_antitone (Fin.le_iff_val_le_val.mpr hk))
    have hcard : (i : ℕ) + 1 ≤ #(univ.filter fun k : Fin (Fintype.card n) => (k : ℕ) ≤ i) := by
      have e : (univ.filter fun k : Fin (Fintype.card n) => (k : ℕ) ≤ i) = Finset.Iic i := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Fin.le_def]
      rw [e, Fin.card_Iic]
    have := (Finset.card_le_card hsub).trans hposcount
    omega
  -- the top `r` eigenvalues carry at least `2r`
  have htop : (2 * r : ℝ) ≤ topEigenvalueSum hH r := by
    rcases le_or_gt (Fintype.card n) r with hkn | hkn
    · rw [topEigenvalueSum_of_card_le hH hkn, rtrace, hHAB, trace_sub]
      have := (re_trace_mul_projection_mem hA₀G (isHermitian_one) (by rw [one_mul])).2
      have h0 := re_trace_nonneg_of_posSemidef hA₀G
      simp only [trace_sub, Complex.sub_re] at h0
      simp only [RCLike.re_to_complex, Complex.sub_re]
      linarith
    · obtain ⟨E, hE, hEE, hErank, hEG⟩ :=
        exists_projection_rank_eq_of_rank_le hG.isHermitian hGrank hkn.le
      have hky := re_trace_mul_projection_le hH hE hEE
      rw [hErank] at hky
      have hGE : (G * E).trace = G.trace := by rw [trace_mul_comm, hEG]
      have hAE := (re_trace_mul_projection_mem hA₀G hE hEE).1
      have hBE := (re_trace_mul_projection_mem hB hE hEE).2
      have hsplit : (H * E).trace = ((A₀ - G) * E).trace + (G * E).trace - (B * E).trace := by
        rw [hHAB, sub_mul, sub_mul, trace_sub, trace_sub]; ring
      rw [hsplit, hGE] at hky
      simp only [RCLike.re_to_complex, Complex.sub_re, Complex.add_re] at hky
      linarith
  exact sum_le_of_isInertiaCertificate _ hpos htop hq

omit [DecidableEq n] in
theorem posSemidef_sum_vecMulVec {ι : Type*} [Fintype ι] (u : ι → n → ℂ) :
    (∑ j, vecMulVec (u j) (star (u j))).PosSemidef :=
  posSemidef_sum _ fun j _ => posSemidef_vecMulVec_self_star (u j)

omit [DecidableEq n] in
/-- A sum of `|ι|` rank-one terms has rank at most `|ι|`. -/
theorem rank_sum_vecMulVec_le {ι : Type*} [Fintype ι] (u : ι → n → ℂ) :
    (∑ j, vecMulVec (u j) (star (u j))).rank ≤ Fintype.card ι := by
  classical
  suffices h : ∀ t : Finset ι, (∑ j ∈ t, vecMulVec (u j) (star (u j))).rank ≤ t.card from
    (h univ).trans (le_of_eq Finset.card_univ)
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.card_insert_of_notMem hj]
    have h1 := rank_vecMulVec_le (u j) (star (u j))
    have h2 := GaloisForLFunctions.HTGeometry.rank_add_le_rank_add_rank
      (vecMulVec (u j) (star (u j))) (∑ j ∈ t, vecMulVec (u j) (star (u j)))
    omega

omit [DecidableEq n] in
theorem re_trace_sum_vecMulVec {ι : Type*} [Fintype ι] (u : ι → n → ℂ) :
    ((∑ j, vecMulVec (u j) (star (u j))).trace).re = ∑ j, ∑ k, Complex.normSq (u j k) := by
  simp only [trace_sum, Complex.re_sum, trace_vecMulVec, dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- **The certificate for explicit columns.** For columns `w_j`, `j ∈ S` (simple critical zeros) and
`a_j`, `j ∈ R` (non-simple blocks), a negative part `B ⪰ 0` and the normalization
`Σ_{j∈R} ‖a_j‖² − tr B ≥ 2|R|`, every admissible weight sums over the spectrum of
`Ĥ = Σ_S w_j w_j* + Σ_R a_j a_j* − B` to at most `|S|`. -/
theorem sum_eigenvalues₀_le_card_of_columns {S R : Type*} [Fintype S] [Fintype R]
    (w : S → n → ℂ) (a : R → n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (hnorm : (2 * Fintype.card R : ℝ) ≤ ∑ j, ∑ k, Complex.normSq (a j k) - (B.trace).re)
    (hH : (∑ j, vecMulVec (w j) (star (w j)) + ∑ j, vecMulVec (a j) (star (a j)) - B).IsHermitian)
    {q : ℝ → ℝ} (hq : IsInertiaCertificate q) :
    ∑ i, q (hH.eigenvalues₀ i) ≤ Fintype.card S := by
  have hGS := posSemidef_sum_vecMulVec w
  have hGR := posSemidef_sum_vecMulVec a
  have hA₀G : (∑ j, vecMulVec (w j) (star (w j)) + ∑ j, vecMulVec (a j) (star (a j)) -
      ∑ j, vecMulVec (a j) (star (a j))).PosSemidef := by
    rw [add_sub_cancel_right]; exact hGS
  have hrank := (GaloisForLFunctions.HTGeometry.rank_add_le_rank_add_rank _ _).trans
    (add_le_add (rank_sum_vecMulVec_le w) (rank_sum_vecMulVec_le a))
  exact sum_eigenvalues₀_le_of_isInertiaCertificate hH (hGS.add hGR) hB hGR hA₀G rfl hrank
    (rank_sum_vecMulVec_le a) (by rw [re_trace_sum_vecMulVec]; exact hnorm) hq

/-! ### The weights -/

/-- The rank–trace weight `2x − x²` of the `2/3` theorem. -/
def qRankTrace (x : ℝ) : ℝ := 2 * x - x ^ 2

theorem isInertiaCertificate_rankTrace : IsInertiaCertificate qRankTrace :=
  ⟨fun x => by unfold qRankTrace; nlinarith [sq_nonneg (x - 1)],
    fun x hx => by unfold qRankTrace; nlinarith [sq_nonneg x],
    ⟨2, by norm_num, fun x => by unfold qRankTrace; nlinarith [sq_nonneg (x - 2)]⟩⟩

/-- The quartic weight `q⋆(x) = 1 − (64/49)((x − 1)² − 1/8)²`: equal to `1` at `1 ± √2/4`, to `0` at
`0` and `2`. -/
def qStar (x : ℝ) : ℝ := 1 - 64 / 49 * ((x - 1) ^ 2 - 1 / 8) ^ 2

/-- `q⋆` lies below its tangent at `2`: `(32/7)(2 − x) − q⋆(x) = (16/49)(x − 2)²(4x² + 7)`. -/
theorem qStar_le_tangent (x : ℝ) : qStar x ≤ 32 / 7 * (2 - x) := by
  unfold qStar
  have h : 32 / 7 * (2 - x) - (1 - 64 / 49 * ((x - 1) ^ 2 - 1 / 8) ^ 2) =
      16 / 49 * ((x - 2) ^ 2 * (4 * x ^ 2 + 7)) := by ring
  nlinarith [mul_nonneg (sq_nonneg (x - 2)) (by positivity : (0 : ℝ) ≤ 4 * x ^ 2 + 7)]

theorem isInertiaCertificate_qStar : IsInertiaCertificate qStar :=
  ⟨fun x => by unfold qStar; nlinarith [sq_nonneg ((x - 1) ^ 2 - 1 / 8)],
    fun x hx => by
      unfold qStar
      have h1 : 7 / 8 ≤ (x - 1) ^ 2 - 1 / 8 := by nlinarith
      nlinarith [mul_le_mul h1 h1 (by norm_num) (by linarith)],
    ⟨32 / 7, by norm_num, qStar_le_tangent⟩⟩

/-- `q⋆` is the quartic `−(64/49)(x⁴ − 4x³ + (23/4)x² − (7/2)x)`; in particular `q⋆(0) = 0`. -/
theorem qStar_eq (x : ℝ) :
    qStar x = 64 / 49 * (-x ^ 4 + 4 * x ^ 3 - 23 / 4 * x ^ 2 + 7 / 2 * x) := by
  unfold qStar; ring

/-- **`q⋆` in moments**: `Σ q⋆(μ_i) = (64/49)(−tr Ĥ⁴ + 4 tr Ĥ³ − (23/4) tr Ĥ² + (7/2) tr Ĥ)`. -/
theorem sum_qStar_eq_moments {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∑ i, qStar (hH.eigenvalues₀ i) = 64 / 49 * (-((H ^ 4).trace).re + 4 * ((H ^ 3).trace).re -
      23 / 4 * ((H ^ 2).trace).re + 7 / 2 * ((H ^ 1).trace).re) := by
  have e : ∀ k : ℕ, ((H ^ k).trace).re = ∑ i, hH.eigenvalues i ^ k := fun k =>
    (GaloisForLFunctions.HTGeometry.sum_pow_eigenvalues_eq_trace_pow_re' hH k).symm
  rw [← sum_eigenvalues_reindex hH qStar, e 4, e 3, e 2, e 1]
  simp only [qStar_eq, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **The quartic census.** On the zero-side model,
`|S| ≥ (64/49)(−tr Ĥ⁴ + 4 tr Ĥ³ − (23/4) tr Ĥ² + (7/2) tr Ĥ)`. -/
theorem qStar_moments_le_card_of_columns {S R : Type*} [Fintype S] [Fintype R]
    (w : S → n → ℂ) (a : R → n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (hnorm : (2 * Fintype.card R : ℝ) ≤ ∑ j, ∑ k, Complex.normSq (a j k) - (B.trace).re)
    (hH : (∑ j, vecMulVec (w j) (star (w j)) + ∑ j, vecMulVec (a j) (star (a j)) - B).IsHermitian) :
    let H := ∑ j, vecMulVec (w j) (star (w j)) + ∑ j, vecMulVec (a j) (star (a j)) - B
    64 / 49 * (-((H ^ 4).trace).re + 4 * ((H ^ 3).trace).re - 23 / 4 * ((H ^ 2).trace).re +
      7 / 2 * ((H ^ 1).trace).re) ≤ Fintype.card S := by
  intro H
  rw [← sum_qStar_eq_moments hH]
  exact sum_eigenvalues₀_le_card_of_columns w a hB hnorm hH isInertiaCertificate_qStar

/-! ### The number -/

/-- The value of `q⋆` at normalized moments `(1, κ₂, κ₃, κ₄)`. -/
def qStarValue (κ₂ κ₃ κ₄ : ℝ) : ℝ := 64 / 49 * (-κ₄ + 4 * κ₃ - 23 / 4 * κ₂ + 7 / 2)

/-- **At the sine-kernel moments `(4/3, 2, 13/4)` the certificate is `16/21`.** -/
theorem qStar_value_sineMoments : qStarValue (4 / 3) 2 (13 / 4) = 16 / 21 := by
  unfold qStarValue; norm_num

theorem three_quarters_lt_sixteen_twentyFirsts : (3 : ℝ) / 4 < 16 / 21 := by norm_num

/-- **The fourth moment separates the coalescence blind spot.** The extremal configuration
`diag(1^{4k}, 2^{k})` of the `2/3` theorem (`N = 6k`) has normalized moments
`((4 + 2^j)/6)_{j=2,3,4} = (4/3, 2, 10/3)`: the first three agree with the sine kernel, the fourth
does not, and there `q⋆` certifies only `32/49 < 2/3`. -/
theorem extremalDiag_moments :
    ((4 : ℝ) + 2 ^ 2) / 6 = 4 / 3 ∧ ((4 : ℝ) + 2 ^ 3) / 6 = 2 ∧ ((4 : ℝ) + 2 ^ 4) / 6 = 10 / 3 ∧
      (10 : ℝ) / 3 ≠ 13 / 4 ∧ qStarValue (4 / 3) 2 (10 / 3) = 32 / 49 ∧
        (32 : ℝ) / 49 < 2 / 3 := by
  unfold qStarValue; norm_num

/-! ### Optimality: a configuration with the sine-kernel moments -/

/-- Index types of the witness: sixteen simple pairs (`Fin 16 ⊕ Fin 16`) and five coalesced
pairs (`Fin 5`). -/
abbrev WitnessS := Fin 16 ⊕ Fin 16
abbrev WitnessIdx := WitnessS ⊕ Fin 5

/-- The witness spectrum: `1 + √2/4` and `1 − √2/4` sixteen times each, `2` five times. -/
def witnessVal : WitnessIdx → ℝ :=
  Sum.elim (Sum.elim (fun _ => 1 + Real.sqrt 2 / 4) (fun _ => 1 - Real.sqrt 2 / 4)) fun _ => 2

theorem witnessVal_nonneg (i : WitnessIdx) : 0 ≤ witnessVal i := by
  have h2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h0 := Real.sqrt_nonneg 2
  rcases i with (j | j) | j <;> simp only [witnessVal, Sum.elim_inl, Sum.elim_inr] <;> linarith

/-- Simple columns `√μ_j e_j`. -/
def witnessW (j : WitnessS) : WitnessIdx → ℂ :=
  Pi.single (Sum.inl j) ((Real.sqrt (witnessVal (Sum.inl j)) : ℝ) : ℂ)

/-- Coalesced-pair columns `√2 e_j`. -/
def witnessA (j : Fin 5) : WitnessIdx → ℂ := Pi.single (Sum.inr j) ((Real.sqrt 2 : ℝ) : ℂ)

theorem vecMulVec_single_star (i : WitnessIdx) (x : ℝ) :
    vecMulVec (Pi.single i (x : ℂ)) (star (Pi.single i (x : ℂ))) =
      diagonal (Pi.single i ((x ^ 2 : ℝ) : ℂ)) := by
  ext a b
  rw [vecMulVec_apply, diagonal_apply, Pi.star_apply]
  rcases eq_or_ne a i with rfl | ha
  · rcases eq_or_ne b a with rfl | hb
    · simp [sq, Complex.conj_ofReal]
    · simp [hb, hb.symm]
  · simp [Pi.single_apply, ha]

/-- The witness matrix is diagonal. -/
theorem witness_eq_diagonal :
    ∑ j, vecMulVec (witnessW j) (star (witnessW j)) +
        ∑ j, vecMulVec (witnessA j) (star (witnessA j)) - 0 =
      diagonal fun i => (witnessVal i : ℂ) := by
  have hdiag : ∀ {ι : Type} [Fintype ι] (f : ι → WitnessIdx → ℂ),
      ∑ j, diagonal (f j) = diagonal (∑ j, f j) := fun f =>
    (map_sum (diagonalAddMonoidHom WitnessIdx ℂ) f Finset.univ).symm
  simp only [witnessW, witnessA, vecMulVec_single_star, sub_zero, hdiag, diagonal_add]
  congr 1
  funext i
  rcases i with j | j
  · simp only [Finset.sum_apply, Pi.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false,
      Finset.sum_const_zero, add_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Real.sq_sqrt (witnessVal_nonneg _)]
  · simp only [Finset.sum_apply, Pi.single_apply, Sum.inr.injEq, reduceCtorEq, ite_false,
      Finset.sum_const_zero, zero_add, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    simp [witnessVal]

theorem witness_isHermitian :
    (∑ j, vecMulVec (witnessW j) (star (witnessW j)) +
        ∑ j, vecMulVec (witnessA j) (star (witnessA j)) - 0).IsHermitian := by
  rw [witness_eq_diagonal]
  exact isHermitian_diagonal_of_self_adjoint _ (by ext i; simp [Complex.conj_ofReal])

/-- The coalesced pairs carry trace `2` each: `Σ ‖a_j‖² − tr 0 = 10 = 2·5`. -/
theorem witness_norm :
    (2 * Fintype.card (Fin 5) : ℝ) ≤
      ∑ j, ∑ k, Complex.normSq (witnessA j k) - ((0 : Matrix WitnessIdx WitnessIdx ℂ).trace).re := by
  have h : ∀ j : Fin 5, ∑ k, Complex.normSq (witnessA j k) = 2 := fun j => by
    rw [Finset.sum_eq_single (Sum.inr j)]
    · simp [witnessA, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · intro b _ hb; simp [witnessA, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp [h]
  norm_num

/-- **The witness has the sine-kernel moments**: `tr Ĥ^k = 42 κ_k` with
`(κ₁, κ₂, κ₃, κ₄) = (1, 4/3, 2, 13/4)`. -/
theorem witness_moments :
    let H : Matrix WitnessIdx WitnessIdx ℂ := diagonal fun i => (witnessVal i : ℂ)
    ((H ^ 1).trace).re = 42 ∧ ((H ^ 2).trace).re = 42 * (4 / 3) ∧ ((H ^ 3).trace).re = 42 * 2 ∧
      ((H ^ 4).trace).re = 42 * (13 / 4) := by
  intro H
  have hc : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htr : ∀ k : ℕ, ((H ^ k).trace).re =
      16 * (1 + Real.sqrt 2 / 4) ^ k + 16 * (1 - Real.sqrt 2 / 4) ^ k + 5 * 2 ^ k := by
    intro k
    have e : (H ^ k).trace = ((16 * (1 + Real.sqrt 2 / 4) ^ k + 16 * (1 - Real.sqrt 2 / 4) ^ k +
        5 * 2 ^ k : ℝ) : ℂ) := by
      simp only [H, diagonal_pow, trace_diagonal, Pi.pow_apply, Fintype.sum_sum_type, witnessVal,
        Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      ring
    rw [e, Complex.ofReal_re]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [htr] <;> ring_nf <;> rw [hc] <;> norm_num
  all_goals nlinarith [hc]

/-- **Optimality of `16/21`.** Every polynomial weight `x ↦ c₁x + c₂x² + c₃x³ + c₄x⁴` whose census
inequality holds on the witness configuration (thirty-two simple zeros of forty-two) has value at
most `16/21` at the sine-kernel moments; `q⋆` attains it. -/
theorem le_sixteen_twentyFirsts_of_valid (c₁ c₂ c₃ c₄ : ℝ)
    (hvalid : ∑ i, (c₁ * witness_isHermitian.eigenvalues₀ i +
      c₂ * witness_isHermitian.eigenvalues₀ i ^ 2 + c₃ * witness_isHermitian.eigenvalues₀ i ^ 3 +
        c₄ * witness_isHermitian.eigenvalues₀ i ^ 4) ≤ Fintype.card WitnessS) :
    c₁ + c₂ * (4 / 3) + c₃ * 2 + c₄ * (13 / 4) ≤ 16 / 21 := by
  have hH := witness_isHermitian
  have hmom := witness_moments
  set H := ∑ j, vecMulVec (witnessW j) (star (witnessW j)) +
    ∑ j, vecMulVec (witnessA j) (star (witnessA j)) - 0
  have hHd : H = diagonal fun i => (witnessVal i : ℂ) := witness_eq_diagonal
  have hsum : ∑ i, (c₁ * hH.eigenvalues₀ i + c₂ * hH.eigenvalues₀ i ^ 2 +
      c₃ * hH.eigenvalues₀ i ^ 3 + c₄ * hH.eigenvalues₀ i ^ 4) =
      c₁ * ((H ^ 1).trace).re + c₂ * ((H ^ 2).trace).re + c₃ * ((H ^ 3).trace).re +
        c₄ * ((H ^ 4).trace).re := by
    have e : ∀ k : ℕ, ((H ^ k).trace).re = ∑ i, hH.eigenvalues i ^ k := fun k =>
      (GaloisForLFunctions.HTGeometry.sum_pow_eigenvalues_eq_trace_pow_re' hH k).symm
    rw [← sum_eigenvalues_reindex hH (fun x => c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4),
      e 4, e 3, e 2, e 1]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, pow_one]
  rw [hsum, hHd] at hvalid
  obtain ⟨h1, h2, h3, h4⟩ := hmom
  rw [h1, h2, h3, h4] at hvalid
  simp only [Fintype.card_sum, Fintype.card_fin] at hvalid
  norm_num at hvalid
  linarith

/-- `q⋆` attains the bound on the witness: thirty-two of forty-two. -/
theorem sum_qStar_witness : ∑ i, qStar (witness_isHermitian.eigenvalues₀ i) = 32 := by
  rw [sum_qStar_eq_moments]
  have hHd : (∑ j, vecMulVec (witnessW j) (star (witnessW j)) +
      ∑ j, vecMulVec (witnessA j) (star (witnessA j)) - 0) =
      diagonal fun i => (witnessVal i : ℂ) := witness_eq_diagonal
  obtain ⟨h1, h2, h3, h4⟩ := witness_moments
  rw [hHd, h1, h2, h3, h4]
  norm_num

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HigherInertia
