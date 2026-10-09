import GaloisForLFunctions.RHTower.LeeYangSplitCountDifference
import GaloisForLFunctions.RHTower.LeeYangDatumFirstZero

/-!
# The field-density budget of Lee–Yang restrictions

Let `L` be a Lee–Yang datum, affine and present in every field (`deg_{u_j} P = 1`), with
frequencies `λ_j`. For every `ε > 0` and `T > 0`, the restriction `f(t) = P(e^{−iλ₁t}, …)` has at
least `Σ_j ⌊(λ_j − ε)T/2π⌋` zeros in `(0, T]`, counted with multiplicity
(`sum_floor_le_zeroCount`).

Slow fields cost nothing: a field with `λ_jT < 2π` contributes `0`, not a negative amount. This is
what makes the bound usable for data with many slow fields.

**Proof.** Lower the frequencies one field at a time to `ε`, inside the same datum (the stability
conditions do not involve the frequencies). Splitting `P = A + u_jB`, the pair `(A, B)` is an
inner split (`LeeYangSplitCount.InnerSplit`) and does not depend on `λ_j`, so each step gains
`⌊(λ_j − ε)T/2π⌋` zeros (`LeeYangSplitCount.zeroCount_sub_ge`).
-/

open Complex Set Filter Topology

namespace RHTower.LeeYangCount

noncomputable section

variable {ι : Type*} [Fintype ι]

namespace LeeYangDatum

/-- The same polynomial with new frequencies. -/
def withFreqs (L : LeeYangDatum ι) (f : ι → ℝ) (hf : ∀ j, 0 < f j) : LeeYangDatum ι :=
  { L with freq := f, freq_pos := hf }

@[simp] theorem withFreqs_P (L : LeeYangDatum ι) (f : ι → ℝ) (hf : ∀ j, 0 < f j) :
    (L.withFreqs f hf).P = L.P := rfl

@[simp] theorem withFreqs_freq (L : LeeYangDatum ι) (f : ι → ℝ) (hf : ∀ j, 0 < f j) :
    (L.withFreqs f hf).freq = f := rfl

theorem withFreqs_self (L : LeeYangDatum ι) : L.withFreqs L.freq L.freq_pos = L := rfl

theorem ext_of_freq {L₁ L₂ : LeeYangDatum ι} (hP : L₁.P = L₂.P) (hf : L₁.freq = L₂.freq) :
    L₁ = L₂ := by
  cases L₁; cases L₂
  simp only at hP hf
  subst hP hf
  rfl

variable [DecidableEq ι]

/-- Data with the same polynomial and the same frequencies off `j` have the same split at `j`. -/
theorem fieldVec_update_eq {L₁ L₂ : LeeYangDatum ι} {j : ι}
    (hf : ∀ k, k ≠ j → L₁.freq k = L₂.freq k) (t y : ℂ) :
    Function.update (L₁.fieldVec t) j y = Function.update (L₂.fieldVec t) j y := by
  funext k
  by_cases hk : k = j
  · subst hk; simp
  · simp only [Function.update_of_ne hk, fieldVec, field, hf k hk]

theorem splitA_eq_of_freq {L₁ L₂ : LeeYangDatum ι} {j : ι} (hP : L₁.P = L₂.P)
    (hf : ∀ k, k ≠ j → L₁.freq k = L₂.freq k) : L₁.splitA j = L₂.splitA j := by
  funext t
  simp only [splitA, fieldVec_update_eq hf, hP]

theorem splitB_eq_of_freq {L₁ L₂ : LeeYangDatum ι} {j : ι} (hP : L₁.P = L₂.P)
    (hf : ∀ k, k ≠ j → L₁.freq k = L₂.freq k) : L₁.splitB j = L₂.splitB j := by
  funext t
  simp only [splitB, fieldVec_update_eq hf, hP, splitA_eq_of_freq hP hf]

/-- The restriction is `f_{λ_j}` for the split at `j`. -/
theorem restr_eq_splitFn (L : LeeYangDatum ι) (j : ι) (hj : L.P.degreeOf j = 1) :
    L.restr = LeeYangSplitCount.splitFn (L.splitA j) (L.splitB j) (L.freq j) := by
  funext t
  rw [L.restr_eq_split j hj.le t, LeeYangSplitCount.splitFn, field]

/-- The split at a field is an inner split. -/
theorem innerSplit (L : LeeYangDatum ι) (j : ι) (hj : L.P.degreeOf j = 1) :
    LeeYangSplitCount.InnerSplit (L.splitA j) (L.splitB j) where
  da := L.differentiable_splitA j
  db := L.differentiable_splitB j
  low := fun z hz => L.splitA_ne_zero_and_norm_splitB_le j hj.le hz
  up := fun z hz => by
    have hle := L.norm_splitA_le_norm_splitB j hj hz
    refine ⟨fun hB => ?_, hle⟩
    have hA : L.splitA j z = 0 := by
      rw [hB, norm_zero] at hle; exact norm_le_zero_iff.mp hle
    have hr := L.restr_eq_split j hj.le z
    rw [hA, hB, zero_mul, add_zero] at hr
    exact L.restr_ne_zero_of_im_ne_zero hz.ne' hr

/-! ## Zero counts on `(0, T]` -/

omit [DecidableEq ι] in
theorem finite_zeros (L : LeeYangDatum ι) (T : ℝ) :
    {z : ℂ | z.im = 0 ∧ z.re ∈ Ioc 0 T ∧ L.restr z = 0}.Finite := by
  have hfin := RHTower.entire_zeros_closedRectangle_finite L.analyticOnNhd_restr
    ⟨I, L.restr_ne_zero_of_im_ne_zero (by simp)⟩ (0 : ℂ) ((T : ℂ) + I)
  refine hfin.subset fun z ⟨him, hre, hz⟩ => ⟨?_, hz⟩
  rw [Complex.mem_reProdIm]
  simp only [zero_re, add_re, ofReal_re, I_re, add_zero, zero_im, add_im, ofReal_im, I_im,
    zero_add]
  rw [uIcc_of_le (by linarith [hre.1, hre.2]), uIcc_of_le zero_le_one, him]
  exact ⟨⟨hre.1.le, hre.2⟩, ⟨le_refl 0, zero_le_one⟩⟩

omit [DecidableEq ι] in
/-- The zeros in `(0, T]`. -/
def zeroSet (L : LeeYangDatum ι) (T : ℝ) : Finset ℂ := (L.finite_zeros T).toFinset

omit [DecidableEq ι] in
theorem mem_zeroSet (L : LeeYangDatum ι) (T : ℝ) (z : ℂ) :
    z ∈ L.zeroSet T ↔ z.im = 0 ∧ z.re ∈ Ioc 0 T ∧ L.restr z = 0 := by
  rw [zeroSet, Set.Finite.mem_toFinset]; rfl

omit [DecidableEq ι] in
/-- The number of zeros in `(0, T]`, with multiplicity. -/
def zeroCount (L : LeeYangDatum ι) (T : ℝ) : ℝ :=
  ∑ w ∈ L.zeroSet T, ((analyticOrderAt L.restr w).toNat : ℝ)

omit [DecidableEq ι] in
theorem zeroCount_nonneg (L : LeeYangDatum ι) (T : ℝ) : 0 ≤ L.zeroCount T :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **One step.** Lowering the frequency of a present field from `λ_j` to `ε < λ_j` loses at least
`⌊(λ_j − ε)T/2π⌋` zeros in `(0, T]`. -/
theorem zeroCount_lower_add_floor_le (L : LeeYangDatum ι) (j : ι) (hj : L.P.degreeOf j = 1)
    {eps T : ℝ} (heps : 0 < eps) (hlt : eps < L.freq j) (hT : 0 < T) :
    (L.withFreqs (Function.update L.freq j eps) (fun k => by
        by_cases hk : k = j
        · subst hk; simpa using heps
        · simpa [Function.update_of_ne hk] using L.freq_pos k)).zeroCount T +
      (⌊(L.freq j - eps) * T / (2 * Real.pi)⌋ : ℝ) ≤ L.zeroCount T := by
  set L' := L.withFreqs (Function.update L.freq j eps) (fun k => by
        by_cases hk : k = j
        · subst hk; simpa using heps
        · simpa [Function.update_of_ne hk] using L.freq_pos k) with hL'
  have hP : L'.P = L.P := rfl
  have hoff : ∀ k, k ≠ j → L'.freq k = L.freq k := fun k hk => by
    simp [hL', Function.update_of_ne hk]
  have hj' : L'.P.degreeOf j = 1 := hj
  have hA : L'.splitA j = L.splitA j := splitA_eq_of_freq hP hoff
  have hB : L'.splitB j = L.splitB j := splitB_eq_of_freq hP hoff
  have hfreq' : L'.freq j = eps := by simp [hL']
  have hr : L.restr = LeeYangSplitCount.splitFn (L.splitA j) (L.splitB j) (L.freq j) :=
    L.restr_eq_splitFn j hj
  have hr' : L'.restr = LeeYangSplitCount.splitFn (L.splitA j) (L.splitB j) eps := by
    rw [L'.restr_eq_splitFn j hj', hA, hB, hfreq']
  have h := LeeYangSplitCount.zeroCount_sub_ge (L.innerSplit j hj) heps hlt hT
    (L.zeroSet T) (L'.zeroSet T)
    (fun z => by rw [mem_zeroSet, hr])
    (fun z => by rw [mem_zeroSet, hr'])
  unfold zeroCount
  rw [hr, hr']
  linarith

/-! ## Lowering all fields -/

/-- Frequencies lowered to `ε` on the fields of `s` that are faster than `ε`. -/
def lowFreq (L : LeeYangDatum ι) (eps : ℝ) (s : Finset ι) : ι → ℝ :=
  fun k => if k ∈ s ∧ eps < L.freq k then eps else L.freq k

theorem lowFreq_pos (L : LeeYangDatum ι) {eps : ℝ} (heps : 0 < eps) (s : Finset ι) (k : ι) :
    0 < L.lowFreq eps s k := by
  unfold lowFreq
  split_ifs
  · exact heps
  · exact L.freq_pos k

/-- The gain `⌊(λ_k − ε)T/2π⌋` of a field faster than `ε`, and `0` otherwise. -/
def fieldGain (L : LeeYangDatum ι) (eps T : ℝ) (k : ι) : ℝ :=
  if eps < L.freq k then (⌊(L.freq k - eps) * T / (2 * Real.pi)⌋ : ℝ) else 0

omit [DecidableEq ι] in
theorem floor_le_fieldGain (L : LeeYangDatum ι) {eps T : ℝ} (hT : 0 < T) (k : ι) :
    (⌊(L.freq k - eps) * T / (2 * Real.pi)⌋ : ℝ) ≤ L.fieldGain eps T k := by
  unfold fieldGain
  split_ifs with h
  · exact le_rfl
  · push Not at h
    have : (L.freq k - eps) * T / (2 * Real.pi) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hT.le)
        (by positivity)
    have h2 : ⌊(L.freq k - eps) * T / (2 * Real.pi)⌋ ≤ 0 := Int.floor_nonpos this
    exact_mod_cast h2

theorem zeroCount_lowFreq_add_le (L : LeeYangDatum ι) (hdeg : ∀ j, L.P.degreeOf j = 1)
    {eps T : ℝ} (heps : 0 < eps) (hT : 0 < T) (s : Finset ι) :
    (L.withFreqs (L.lowFreq eps s) (L.lowFreq_pos heps s)).zeroCount T +
      ∑ k ∈ s, L.fieldGain eps T k ≤ L.zeroCount T := by
  induction s using Finset.induction_on with
  | empty =>
    have hfreq : L.lowFreq eps ∅ = L.freq := funext fun k => by simp [lowFreq]
    have hL : L.withFreqs (L.lowFreq eps ∅) (L.lowFreq_pos heps ∅) = L :=
      ext_of_freq rfl (by simpa using hfreq)
    rw [hL, Finset.sum_empty, add_zero]
  | insert k s hk ih =>
    set M := L.withFreqs (L.lowFreq eps s) (L.lowFreq_pos heps s) with hM
    have hMk : M.freq k = L.freq k := by simp [hM, lowFreq, hk]
    rw [Finset.sum_insert hk]
    by_cases hlt : eps < L.freq k
    · have hdegM : M.P.degreeOf k = 1 := hdeg k
      have hstep := M.zeroCount_lower_add_floor_le k hdegM heps (by rw [hMk]; exact hlt) hT
      have hfreq : L.lowFreq eps (insert k s) = Function.update M.freq k eps := by
        funext m
        by_cases hm : m = k
        · subst hm; simp [lowFreq, hlt]
        · simp [lowFreq, hM, Finset.mem_insert, hm]
      have hL : L.withFreqs (L.lowFreq eps (insert k s)) (L.lowFreq_pos heps (insert k s)) =
          M.withFreqs (Function.update M.freq k eps) (fun m => by
            by_cases hm : m = k
            · subst hm; simpa using heps
            · simpa [Function.update_of_ne hm] using M.freq_pos m) :=
        ext_of_freq rfl (by simpa using hfreq)
      rw [hL]
      have hgain : L.fieldGain eps T k = (⌊(M.freq k - eps) * T / (2 * Real.pi)⌋ : ℝ) := by
        simp [fieldGain, hlt, hMk]
      linarith
    · have hfreq : L.lowFreq eps (insert k s) = L.lowFreq eps s := by
        funext m
        by_cases hm : m = k
        · subst hm; simp [lowFreq, hlt, hk]
        · simp [lowFreq, Finset.mem_insert, hm]
      have hL : L.withFreqs (L.lowFreq eps (insert k s)) (L.lowFreq_pos heps (insert k s)) = M :=
        ext_of_freq rfl (by simpa [hM] using hfreq)
      rw [hL]
      have hgain : L.fieldGain eps T k = 0 := by simp [fieldGain, hlt]
      linarith

/-- **The field-density budget.** A Lee–Yang datum affine and present in every field has, for every
`ε > 0` and `T > 0`, at least `Σ_j ⌊(λ_j − ε)T/2π⌋` zeros in `(0, T]` with multiplicity. -/
theorem sum_floor_le_zeroCount (L : LeeYangDatum ι) (hdeg : ∀ j, L.P.degreeOf j = 1)
    {eps T : ℝ} (heps : 0 < eps) (hT : 0 < T) :
    ∑ j, (⌊(L.freq j - eps) * T / (2 * Real.pi)⌋ : ℝ) ≤ L.zeroCount T := by
  have h := L.zeroCount_lowFreq_add_le hdeg heps hT Finset.univ
  have h0 := (L.withFreqs (L.lowFreq eps Finset.univ) (L.lowFreq_pos heps Finset.univ)).zeroCount_nonneg T
  calc ∑ j, (⌊(L.freq j - eps) * T / (2 * Real.pi)⌋ : ℝ) ≤ ∑ j, L.fieldGain eps T j :=
        Finset.sum_le_sum fun j _ => L.floor_le_fieldGain hT j
    _ ≤ L.zeroCount T := by linarith

omit [DecidableEq ι] in
theorem ceil_sub_one_le_floor_sub {x δ : ℝ} (hδ : δ ≤ x - ⌈x⌉ + 1) :
    ((⌈x⌉ : ℤ) : ℝ) - 1 ≤ (⌊x - δ⌋ : ℝ) := by
  have h : ⌈x⌉ - 1 ≤ ⌊x - δ⌋ := by
    rw [Int.le_floor]; push_cast; linarith
  exact_mod_cast h

/-- **The budget without `ε`.** `Σ_j (⌈λ_jT/2π⌉ − 1) ≤ N(T)`; this is `Σ_j ⌊λ_jT/2π⌋` when no
`λ_jT/2π` is an integer. -/
theorem sum_ceil_sub_one_le_zeroCount (L : LeeYangDatum ι) (hdeg : ∀ j, L.P.degreeOf j = 1)
    {T : ℝ} (hT : 0 < T) :
    ∑ j, (((⌈L.freq j * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) ≤ L.zeroCount T := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  -- a small `ε` that keeps every floor at `⌈x_j⌉ − 1`
  have hev : ∀ᶠ eps in 𝓝[>] (0 : ℝ), 0 < eps ∧ ∀ j, eps * T / (2 * Real.pi) ≤
      L.freq j * T / (2 * Real.pi) - ⌈L.freq j * T / (2 * Real.pi)⌉ + 1 := by
    refine (eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)).and
      (Filter.eventually_all.mpr fun j => ?_)
    have hpos : 0 < L.freq j * T / (2 * Real.pi) - ⌈L.freq j * T / (2 * Real.pi)⌉ + 1 := by
      have := Int.ceil_lt_add_one (L.freq j * T / (2 * Real.pi)); linarith
    have hc : Continuous fun eps : ℝ => eps * T / (2 * Real.pi) := by fun_prop
    have ht : Tendsto (fun eps : ℝ => eps * T / (2 * Real.pi)) (𝓝[>] 0) (𝓝 0) := by
      have := hc.tendsto 0
      simp only [zero_mul, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact (ht.eventually (ge_mem_nhds hpos))
  obtain ⟨eps, heps, hsmall⟩ := hev.exists
  have hmain := L.sum_floor_le_zeroCount hdeg heps hT
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) hmain
  have hrw : (L.freq j - eps) * T / (2 * Real.pi) =
      L.freq j * T / (2 * Real.pi) - eps * T / (2 * Real.pi) := by ring
  rw [hrw]
  exact ceil_sub_one_le_floor_sub (hsmall j)

end LeeYangDatum

end

end RHTower.LeeYangCount
