import GaloisForLFunctions.RHTower.RankTraceBoundAfterRemovingABlock
import GaloisForLFunctions.RHTower.RiemannGaussian.EtaEnergyFiniteWindowInertia
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum

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

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HigherInertia

open RiemannGaussian.HermitianRankTrace RHTower

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
  simp only [Complex.re_sum, RCLike.ofReal_re]
  exact Finset.sum_nonneg fun i _ => hM.eigenvalues_nonneg i

/-- Against an orthogonal projection, a positive semidefinite matrix has trace between `0` and its
own trace. -/
theorem re_trace_mul_projection_mem {M E : Matrix n n ℂ} (hM : M.PosSemidef) (hE : E.IsHermitian)
    (hEE : E * E = E) :
    0 ≤ ((M * E).trace).re ∧ ((M * E).trace).re ≤ (M.trace).re := by
  have hcomp : ∀ F : Matrix n n ℂ, F.IsHermitian → F * F = F →
      (M * F).trace = (Fᴴ * M * F).trace := fun F hF hFF => by
    rw [hF.eq, trace_mul_comm, ← mul_assoc, ← hFF, mul_assoc F F, trace_mul_comm F, mul_assoc]
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
    have hpi : posIndex (hA₀.isHermitian.sub hB.isHermitian) = posIndex hH := by
      subst hHAB; rfl
    rw [hpi, posIndex, card_eigenvalues_reindex hH (fun x => 0 < x)] at h
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
      calc (i : ℕ) + 1 = #(Finset.range ((i : ℕ) + 1)) := (Finset.card_range _).symm
        _ ≤ _ := Finset.card_le_card_of_injOn (fun k => (⟨k, by omega⟩ : Fin (Fintype.card n)))
            (fun k hk => by
              simp only [Finset.coe_range, Set.mem_Iio] at hk
              simp only [Finset.coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
              omega)
            (fun a _ b _ h => by simpa using h)
    have := (Finset.card_le_card hsub).trans hposcount
    omega
  -- the top `r` eigenvalues carry at least `2r`
  have htop : (2 * r : ℝ) ≤ topEigenvalueSum hH r := by
    rcases le_or_gt (Fintype.card n) r with hkn | hkn
    · rw [topEigenvalueSum_of_card_le hH hkn, rtrace, hHAB, trace_sub]
      have := (re_trace_mul_projection_mem hA₀G (isHermitian_one) (by rw [one_mul])).2
      have h0 := re_trace_nonneg_of_posSemidef hA₀G
      simp only [mul_one, trace_sub, Complex.sub_re] at h0
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

/-- **The certificate for explicit columns.** For columns `w_j`, `j ∈ S` (simple critical zeros) and
`j ∈ R` (non-simple blocks), a negative part `B ⪰ 0` and the normalization
`Σ_{j∈R} ‖w_j‖² − tr B ≥ 2|R|`, every admissible weight sums over the spectrum of
`Ĥ = Σ_{S ∪ R} w_j w_j* − B` to at most `|S|`. -/
theorem sum_eigenvalues₀_le_card_of_columns {S R : Type*} [Fintype S] [Fintype R]
    (w : S → n → ℂ) (a : R → n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (hnorm : (2 * Fintype.card R : ℝ) ≤ ∑ j, ∑ k, Complex.normSq (a j k) - (B.trace).re)
    (hH : (∑ j, vecMulVec (w j) (star (w j)) + ∑ j, vecMulVec (a j) (star (a j)) - B).IsHermitian)
    {q : ℝ → ℝ} (hq : IsInertiaCertificate q) :
    ∑ i, q (hH.eigenvalues₀ i) ≤ Fintype.card S := by
  set GS : Matrix n n ℂ := ∑ j, vecMulVec (w j) (star (w j))
  set GR : Matrix n n ℂ := ∑ j, vecMulVec (a j) (star (a j))
  have hrk1 : ∀ v : n → ℂ, (vecMulVec v (star v)).PosSemidef ∧ (vecMulVec v (star v)).rank ≤ 1 :=
    fun v => ⟨Matrix.posSemidef_vecMulVec_self_star v, rank_vecMulVec_le v (star v)⟩
  have hsum_rank : ∀ {ι : Type*} [Fintype ι] (u : ι → n → ℂ),
      (∑ j, vecMulVec (u j) (star (u j))).rank ≤ Fintype.card ι := fun u => by
    classical
    refine (rank_sum_le _ _).trans ?_
    calc ∑ j, (vecMulVec (u j) (star (u j))).rank ≤ ∑ _j : _, 1 :=
          Finset.sum_le_sum fun j _ => (hrk1 (u j)).2
      _ = _ := by simp
  have hpsd : ∀ {ι : Type*} [Fintype ι] (u : ι → n → ℂ),
      (∑ j, vecMulVec (u j) (star (u j))).PosSemidef := fun u =>
    Matrix.posSemidef_sum _ fun j _ => (hrk1 (u j)).1
  have hGR := hpsd a
  have hGS := hpsd w
  have hA₀ : (GS + GR).PosSemidef := hGS.add hGR
  have hA₀G : (GS + GR - GR).PosSemidef := by rw [add_sub_cancel_right]; exact hGS
  have hrank : (GS + GR).rank ≤ Fintype.card S + Fintype.card R :=
    (rank_add_le _ _).trans (add_le_add (hsum_rank w) (hsum_rank a))
  have htrGR : (GR.trace).re = ∑ j, ∑ k, Complex.normSq (a j k) := by
    simp only [GR, trace_sum, Complex.re_sum, trace_vecMulVec, dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact sum_eigenvalues₀_le_of_isInertiaCertificate hH hA₀ hB hGR hA₀G rfl hrank
    (hsum_rank a) (by rw [htrGR]; exact hnorm) hq

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HigherInertia
