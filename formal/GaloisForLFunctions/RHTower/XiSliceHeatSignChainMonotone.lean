import GaloisForLFunctions.RHTower.XiSliceHeatTransferNoSlack

/-!
# Heat in the slice variable never creates sign changes

Let `T_n(λ, 0, t)` be the heated slice coefficients.  A *sign chain of length `k`* of a real sequence
is a strictly increasing choice of `k + 1` indices at which the sequence has strictly alternating
signs (`HasSignChain`).

**Theorem** (`DeBruijn.hasSignChain_xiSliceHeatTransfer_of_le`).  For `λ ≤ λ'` and every height `t`,
if `m ↦ Re T_{2m}(λ', 0, t)` has a sign chain of length `k`, so does `m ↦ Re T_{2m}(λ, 0, t)`.
Equivalently, the number of sign changes of the even heated slice coefficients is non-increasing
in the heat, at every height.

Proof.  With `b_m = (2m)! Re T_{2m}(λ, 0, t)` the heat shift reads `b'_m = Σ_k s^k/k! b_{m+k}`,
`s = (λ' − λ)/2` (`hasSum_xiSliceHeatTransfer_shift`), i.e. `b' = e^{sD} b` for the shift `D`.
* One step `b ↦ b + εDb` (`ε ≥ 0`) never creates a sign chain (`HasSignChain.of_add_shift`): wherever
  `b_m + ε b_{m+1}` has a sign, `b_m` or `b_{m+1}` has it, and two consecutive chain positions cannot
  pick the same index.
* `(1 + (s/N)D)^N b → e^{sD} b` pointwise (`tendsto_binomShift`), by dominated convergence with the
  majorant `s^j/j! |b_{m+j}|` and `C(N, j)(s/N)^j → s^j/j!`.
* A sign chain of the limit is a sign chain of every late approximant (`HasSignChain.of_tendsto`).
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- A sign chain of length `k`: indices `i₀ < ⋯ < i_k` at which `b` has strictly alternating signs. -/
def HasSignChain (b : ℕ → ℝ) (k : ℕ) : Prop :=
  ∃ i : Fin (k + 1) → ℕ, StrictMono i ∧ ∃ σ : ℝ, ∀ j : Fin (k + 1), 0 < (-1) ^ (j : ℕ) * σ * b (i j)

theorem neg_one_pow_succ_val {k : ℕ} (j : Fin k) :
    ((-1 : ℝ) ^ ((j.succ : Fin (k + 1)) : ℕ)) = -((-1) ^ ((j.castSucc : Fin (k + 1)) : ℕ)) := by
  rw [Fin.val_succ, Fin.val_castSucc, pow_succ]; ring

/-- **One step does not create sign chains.**  If `m ↦ b_m + ε b_{m+1}` (`ε ≥ 0`) has a sign chain of
length `k`, so does `b`. -/
theorem HasSignChain.of_add_shift {b : ℕ → ℝ} {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ}
    (h : HasSignChain (fun m => b m + ε * b (m + 1)) k) : HasSignChain b k := by
  classical
  obtain ⟨i, hi, σ, hσ⟩ := h
  have hch : ∀ j : Fin (k + 1),
      0 < (-1) ^ (j : ℕ) * σ * b (i j) ∨ 0 < (-1) ^ (j : ℕ) * σ * b (i j + 1) := by
    intro j
    by_contra hcon
    push Not at hcon
    have h1 := hσ j
    have h2 := mul_nonpos_of_nonneg_of_nonpos hε hcon.2
    have e : (-1) ^ (j : ℕ) * σ * (b (i j) + ε * b (i j + 1))
        = (-1) ^ (j : ℕ) * σ * b (i j) + ε * ((-1) ^ (j : ℕ) * σ * b (i j + 1)) := by ring
    simp only at h1
    linarith
  let p : Fin (k + 1) → ℕ := fun j =>
    if 0 < (-1) ^ (j : ℕ) * σ * b (i j) then i j else i j + 1
  have hp : ∀ j : Fin (k + 1), 0 < (-1) ^ (j : ℕ) * σ * b (p j) := by
    intro j
    simp only [p]
    split_ifs with h
    · exact h
    · exact (hch j).resolve_left h
  have hple : ∀ j : Fin (k + 1), i j ≤ p j ∧ p j ≤ i j + 1 := by
    intro j; simp only [p]; split_ifs <;> omega
  refine ⟨p, ?_, σ, hp⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro j
  have h1 := hple j.castSucc
  have h2 := hple j.succ
  have hii : i j.castSucc < i j.succ := hi (Fin.castSucc_lt_succ : j.castSucc < j.succ)
  by_contra hcon
  have heq : p j.castSucc = p j.succ := by omega
  have ha := hp j.castSucc
  have hb := hp j.succ
  rw [← heq, neg_one_pow_succ_val] at hb
  nlinarith

/-- The binomial approximation `((1 + εD)^N b)_m = Σ_{j ≤ N} C(N, j) ε^j b_{m+j}`. -/
def binomShift (ε : ℝ) (N : ℕ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * ε ^ j * b (m + j)

theorem binomShift_zero (ε : ℝ) (b : ℕ → ℝ) (m : ℕ) : binomShift ε 0 b m = b m := by
  simp [binomShift]

theorem binomShift_succ (ε : ℝ) (N : ℕ) (b : ℕ → ℝ) (m : ℕ) :
    binomShift ε (N + 1) b m = binomShift ε N b m + ε * binomShift ε N b (m + 1) := by
  unfold binomShift
  set f : ℕ → ℝ := fun j => (N.choose j : ℝ) * ε ^ (j + 1) * b (m + (j + 1)) with hf
  set g : ℕ → ℝ := fun j => (N.choose (j + 1) : ℝ) * ε ^ (j + 1) * b (m + (j + 1)) with hg
  have hL : ∑ j ∈ Finset.range (N + 1 + 1), ((N + 1).choose j : ℝ) * ε ^ j * b (m + j)
      = ∑ j ∈ Finset.range (N + 1), f j + ∑ j ∈ Finset.range (N + 1), g j + b m := by
    rw [Finset.sum_range_succ', ← Finset.sum_add_distrib]
    simp only [Nat.choose_succ_succ', Nat.cast_add, Nat.choose_zero_right, Nat.cast_one, pow_zero,
      one_mul, add_zero, hf, hg]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hA : ∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * ε ^ j * b (m + j)
      = ∑ j ∈ Finset.range N, g j + b m := by
    rw [Finset.sum_range_succ']
    simp [hg]
  have hG : ∑ j ∈ Finset.range (N + 1), g j = ∑ j ∈ Finset.range N, g j := by
    rw [Finset.sum_range_succ]
    simp [hg]
  have hB : ε * ∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * ε ^ j * b (m + 1 + j)
      = ∑ j ∈ Finset.range (N + 1), f j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hf]
    rw [show m + 1 + j = m + (j + 1) by ring, pow_succ]; ring
  rw [hL, hA, hB, hG]
  ring

/-- `(1 + εD)^N` creates no sign chains. -/
theorem HasSignChain.of_binomShift {b : ℕ → ℝ} {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ} :
    ∀ N : ℕ, HasSignChain (binomShift ε N b) k → HasSignChain b k := by
  intro N
  induction N with
  | zero => intro h; simpa [HasSignChain, binomShift_zero] using h
  | succ N ih =>
    intro h
    refine ih (HasSignChain.of_add_shift hε ?_)
    have e : binomShift ε (N + 1) b = fun m => binomShift ε N b m + ε * binomShift ε N b (m + 1) :=
      funext (binomShift_succ ε N b)
    rwa [e] at h

/-- **Persistence.**  A sign chain of a pointwise limit is a sign chain of some approximant. -/
theorem HasSignChain.of_tendsto {f : ℕ → ℕ → ℝ} {B : ℕ → ℝ} {k : ℕ}
    (hlim : ∀ m, Tendsto (fun N => f N m) atTop (𝓝 (B m))) (h : HasSignChain B k) :
    ∃ N, HasSignChain (f N) k := by
  obtain ⟨i, hi, σ, hσ⟩ := h
  have hev : ∀ j : Fin (k + 1), ∀ᶠ N in atTop, 0 < (-1) ^ (j : ℕ) * σ * f N (i j) := fun j =>
    (tendsto_const_nhds.mul (hlim (i j))).eventually (lt_mem_nhds (hσ j))
  obtain ⟨N, hN⟩ := (Filter.eventually_all.mpr hev).exists
  exact ⟨N, i, hi, σ, hN⟩

/-- Positive rescaling preserves sign chains. -/
theorem HasSignChain.of_pos_mul {b : ℕ → ℝ} {w : ℕ → ℝ} (hw : ∀ m, 0 < w m) {k : ℕ}
    (h : HasSignChain (fun m => w m * b m) k) : HasSignChain b k := by
  obtain ⟨i, hi, σ, hσ⟩ := h
  refine ⟨i, hi, σ, fun j => ?_⟩
  have h1 := hσ j
  have e : (-1) ^ (j : ℕ) * σ * (w (i j) * b (i j)) = w (i j) * ((-1) ^ (j : ℕ) * σ * b (i j)) := by
    ring
  simp only at h1
  rw [e] at h1
  exact pos_of_mul_pos_right h1 (hw _).le

theorem HasSignChain.pos_mul {b : ℕ → ℝ} {w : ℕ → ℝ} (hw : ∀ m, 0 < w m) {k : ℕ}
    (h : HasSignChain b k) : HasSignChain (fun m => w m * b m) k := by
  obtain ⟨i, hi, σ, hσ⟩ := h
  refine ⟨i, hi, σ, fun j => ?_⟩
  have e : (-1) ^ (j : ℕ) * σ * (w (i j) * b (i j)) = w (i j) * ((-1) ^ (j : ℕ) * σ * b (i j)) := by
    ring
  simp only
  rw [e]
  exact mul_pos (hw _) (hσ j)

/-! ## The binomial approximation converges to `e^{sD}` -/

theorem choose_mul_div_pow_le {s : ℝ} (hs : 0 ≤ s) (N j : ℕ) :
    (N.choose j : ℝ) * (s / N) ^ j ≤ s ^ j / j.factorial := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simp
    · rw [Nat.choose_eq_zero_of_lt hj]; simp; positivity
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h := Nat.choose_le_pow_div (α := ℝ) j N
    calc (N.choose j : ℝ) * (s / N) ^ j ≤ (N : ℝ) ^ j / j.factorial * (s / N) ^ j :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = s ^ j / j.factorial := by
          rw [div_pow]; field_simp

theorem tendsto_choose_mul_div_pow (s : ℝ) (j : ℕ) :
    Tendsto (fun N : ℕ => (N.choose j : ℝ) * (s / N) ^ j) atTop (𝓝 (s ^ j / j.factorial)) := by
  -- `C(N, j) (s/N)^j = (D_N/N^j) · s^j/j!` with `D_N` the falling factorial
  set D : ℕ → ℝ := fun N => (N.descFactorial j : ℝ) / (N : ℝ) ^ j with hD
  have hDlim : Tendsto D atTop (𝓝 1) := by
    have hlow : Tendsto (fun N : ℕ => (1 - (j : ℝ) / N) ^ j) atTop (𝓝 1) := by
      have h := ((tendsto_const_div_atTop_nhds_zero_nat (j : ℝ)).const_sub 1).pow j
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop (j + 1)] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      simp only [hD]
      rw [le_div_iff₀ (by positivity), ← mul_pow, sub_mul, div_mul_cancel₀ _ hN0.ne', one_mul]
      have h1 := Nat.pow_sub_le_descFactorial N j
      have h2 : ((N : ℝ) - j) ≤ ((N + 1 - j : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; linarith
      calc ((N : ℝ) - j) ^ j ≤ ((N + 1 - j : ℕ) : ℝ) ^ j :=
            pow_le_pow_left₀ (by linarith [show (j : ℝ) + 1 ≤ N by exact_mod_cast hN]) h2 j
        _ ≤ (N.descFactorial j : ℝ) := by exact_mod_cast h1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      simp only [hD]
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.descFactorial_le_pow N j
  have h := hDlim.mul_const (s ^ j / j.factorial)
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (N.choose j : ℝ) = (N.descFactorial j : ℝ) / j.factorial := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; field_simp
  simp only [hD]
  rw [hc, div_pow]; field_simp

/-- **`(1 + (s/N)D)^N b → e^{sD} b` pointwise.** -/
theorem tendsto_binomShift {s : ℝ} (hs : 0 ≤ s) {b : ℕ → ℝ} (m : ℕ)
    (hsum : Summable fun j => s ^ j / j.factorial * |b (m + j)|) :
    Tendsto (fun N : ℕ => binomShift (s / N) N b m) atTop
      (𝓝 (∑' j, s ^ j / j.factorial * b (m + j))) := by
  classical
  set g : ℕ → ℕ → ℝ := fun N j =>
    if j ≤ N then (N.choose j : ℝ) * (s / N) ^ j * b (m + j) else 0 with hg
  have hgsum : ∀ N : ℕ, binomShift (s / N) N b m = ∑' j, g N j := by
    intro N
    rw [tsum_eq_sum (s := Finset.range (N + 1)) fun j hj => ?_]
    · unfold binomShift
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simp [hg, this]
    · have : ¬ j ≤ N := fun h => hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      simp [hg, this]
  simp_rw [hgsum]
  refine tendsto_tsum_of_dominated_convergence hsum (fun j => ?_)
    (Eventually.of_forall fun N j => ?_)
  · have h := (tendsto_choose_mul_div_pow s j).mul_const (b (m + j))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop j] with N hN
    simp [hg, hN]
  · simp only [hg]
    split_ifs with hjN
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (choose_mul_div_pow_le hs N j) (abs_nonneg _)
    · simp only [norm_zero]; positivity

namespace DeBruijn

/-- **Heat never creates sign changes.**  For `λ ≤ λ'` and every height `t`, a sign chain of length `k`
of the even heated slice coefficients `m ↦ Re T_{2m}(λ', 0, t)` gives one of `m ↦ Re T_{2m}(λ, 0, t)`. -/
theorem hasSignChain_xiSliceHeatTransfer_of_le {lam lam' t : ℝ} (hll : lam ≤ lam') {k : ℕ}
    (h : HasSignChain (fun m => (xiSliceHeatTransfer lam' 0 t (2 * m)).re) k) :
    HasSignChain (fun m => (xiSliceHeatTransfer lam 0 t (2 * m)).re) k := by
  set s := (lam' - lam) / 2 with hsdef
  have hs : 0 ≤ s := by rw [hsdef]; linarith
  set b : ℕ → ℝ := fun m => ((2 * m).factorial : ℝ) * (xiSliceHeatTransfer lam 0 t (2 * m)).re
    with hb
  have hser : ∀ m, HasSum (fun k => s ^ k / k.factorial * b (m + k))
      (((2 * m).factorial : ℝ) * (xiSliceHeatTransfer lam' 0 t (2 * m)).re) := by
    intro m
    have h1 := (Complex.hasSum_re (hasSum_xiSliceHeatTransfer_shift hll 0 t (2 * m))).mul_left
      ((2 * m).factorial : ℝ)
    refine h1.congr_fun fun k => ?_
    simp only [hb]
    rw [Complex.re_ofReal_mul, show 2 * m + 2 * k = 2 * (m + k) by ring]
    have hf : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    rw [hsdef]; ring
  have hsum : ∀ m, Summable fun j => s ^ j / j.factorial * |b (m + j)| := by
    intro m
    refine (summable_abs_iff.mpr (hser m).summable).congr fun j => ?_
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have hlim : ∀ m, Tendsto (fun N : ℕ => binomShift (s / N) N b m) atTop
      (𝓝 (((2 * m).factorial : ℝ) * (xiSliceHeatTransfer lam' 0 t (2 * m)).re)) := by
    intro m
    rw [← (hser m).tsum_eq]
    exact tendsto_binomShift hs m (hsum m)
  have hB : HasSignChain (fun m => ((2 * m).factorial : ℝ) *
      (xiSliceHeatTransfer lam' 0 t (2 * m)).re) k :=
    HasSignChain.pos_mul (fun m => by positivity) h
  obtain ⟨N, hN⟩ := HasSignChain.of_tendsto hlim hB
  have hbN := HasSignChain.of_binomShift (by positivity : (0 : ℝ) ≤ s / N) N hN
  exact HasSignChain.of_pos_mul (fun m => by positivity) hbN

end DeBruijn

end

end RHTower
