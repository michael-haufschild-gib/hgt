import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityOrderK
import GaloisForLFunctions.HTGeometry.ValuatedDeterminantMultilinearity

/-!
# Toeplitz minors after multiplication by a geometric factor

Let `b = a ∗ (yⁿ)` be the Cauchy product of a sequence `a` with the geometric sequence, i.e. the
coefficient sequence of `A(u)/(1 − yu)`.  For strictly increasing columns `j`,

`det (b_{j_c − i_r}) = Σ_l y^{Σ_c (j_c − l_c)} det (a_{l_c − i_r})`,

the sum running over the columns `l` that interlace `j` from below: `l_c ≤ j_c` and
`j_{c−1} < l_c` (`toeplitzMinor_cauchyConv_geometric`).  This is the branching rule of skew Schur
functions, written for Toeplitz minors.

The proof converts the columns from `b` to `a`, starting with the last.  Since
`b_n = a_n + y b_{n−1}`, the `b`-column at `j_c` is `Σ_{t < T} y^t` times the `a`-column at
`j_c − t`, plus `y^T` times the `b`-column at `j_c − T`.  With `T = j_c − j_{c−1}` that last column
repeats column `c − 1`, which is still a `b`-column, so it drops out of the determinant.  For
`c = 0` take `T = j_0 + 1`; the remainder column then vanishes.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `b_n = a_n + y b_{n−1}` for `b = a ∗ (yⁿ)`, extended by zero to the integers. -/
theorem zext_cauchyConv_geometric (a : ℕ → ℝ) (y : ℝ) (z : ℤ) :
    zext (cauchyConv a fun n => y ^ n) z =
      zext a z + y * zext (cauchyConv a fun n => y ^ n) (z - 1) := by
  rcases lt_or_ge z 0 with hz | hz
  · rw [zext_of_neg _ hz, zext_of_neg _ hz, zext_of_neg _ (by omega)]
    ring
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [zext_natCast, zext_natCast]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [zext_of_neg _ (by norm_num)]
      simp [cauchyConv]
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [show ((n' + 1 : ℕ) : ℤ) - 1 = (n' : ℤ) by push_cast; ring, zext_natCast]
      unfold cauchyConv
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, pow_zero, mul_one]
      rw [Finset.mul_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show n' + 1 - k = (n' - k) + 1 by omega, pow_succ]
      ring

/-- Iterating `b_n = a_n + y b_{n−1}` `T` times. -/
theorem zext_cauchyConv_geometric_iterate (a : ℕ → ℝ) (y : ℝ) (z : ℤ) (T : ℕ) :
    zext (cauchyConv a fun n => y ^ n) z =
      (∑ t ∈ range T, y ^ t * zext a (z - t)) +
        y ^ T * zext (cauchyConv a fun n => y ^ n) (z - T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [ih, zext_cauchyConv_geometric a y (z - T), Finset.sum_range_succ]
    push_cast
    rw [show z - (T : ℤ) - 1 = z - ((T : ℤ) + 1) by ring]
    ring

/-- Columns interlacing `j` from below in the first `k` positions, equal to `j` from `k` on. -/
def interlaceSetUpTo {m : ℕ} (j : Fin m → ℕ) (k : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun c => range (j c + 1)).filter fun l =>
    (∀ c : Fin m, k ≤ c.val → l c = j c) ∧
      ∀ c c' : Fin m, c.val < k → c'.val + 1 = c.val → j c' < l c

/-- The columns interlacing `j` from below: `l_c ≤ j_c` and `j_{c−1} < l_c`. -/
def interlaceSet {m : ℕ} (j : Fin m → ℕ) : Finset (Fin m → ℕ) := interlaceSetUpTo j m

theorem mem_interlaceSetUpTo {m : ℕ} {j : Fin m → ℕ} {k : ℕ} {l : Fin m → ℕ} :
    l ∈ interlaceSetUpTo j k ↔ (∀ c, l c ≤ j c) ∧ (∀ c : Fin m, k ≤ c.val → l c = j c) ∧
      ∀ c c' : Fin m, c.val < k → c'.val + 1 = c.val → j c' < l c := by
  simp only [interlaceSetUpTo, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    Nat.lt_succ_iff]

theorem mem_interlaceSet {m : ℕ} {j l : Fin m → ℕ} :
    l ∈ interlaceSet j ↔ (∀ c, l c ≤ j c) ∧ ∀ c c' : Fin m, c'.val + 1 = c.val → j c' < l c := by
  rw [interlaceSet, mem_interlaceSetUpTo]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, fun c c' h => h3 c c' c.isLt h⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, fun c hc => absurd c.isLt (not_lt.mpr hc), fun c c' _ h => h3 c c' h⟩

/-- The mixed minor: columns `c < k` from `b`, columns `c ≥ k` from `a`. -/
def mixMinor (a b : ℕ → ℝ) {m : ℕ} (i j : Fin m → ℕ) (k : ℕ) : ℝ :=
  Matrix.det (Matrix.of fun r c =>
    if c.val < k then zext b ((j c : ℤ) - i r) else zext a ((j c : ℤ) - i r))

theorem mixMinor_zero (a b : ℕ → ℝ) {m : ℕ} (i j : Fin m → ℕ) :
    mixMinor a b i j 0 = toeplitzMinor a m i j := by
  simp [mixMinor, toeplitzMinor]

theorem mixMinor_self (a b : ℕ → ℝ) {m : ℕ} (i j : Fin m → ℕ) :
    mixMinor a b i j m = toeplitzMinor b m i j := by
  simp [mixMinor, toeplitzMinor]

/-- **One column step.**  Converting column `k` from `b = a ∗ (yⁿ)` to `a`. -/
theorem mixMinor_succ (a : ℕ → ℝ) (y : ℝ) {m : ℕ} (i j : Fin m → ℕ) (hj : StrictMono j)
    {k : ℕ} (hk : k < m) :
    mixMinor a (cauchyConv a fun n => y ^ n) i j (k + 1) =
      ∑ t ∈ range (if k = 0 then j ⟨k, hk⟩ + 1 else j ⟨k, hk⟩ - j ⟨k - 1, by omega⟩),
        y ^ t * mixMinor a (cauchyConv a fun n => y ^ n) i
          (Function.update j ⟨k, hk⟩ (j ⟨k, hk⟩ - t)) k := by
  classical
  set b := cauchyConv a fun n => y ^ n with hb
  set ck : Fin m := ⟨k, hk⟩ with hck
  set T := if k = 0 then j ck + 1 else j ck - j ⟨k - 1, by omega⟩ with hT
  set M : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun r c =>
    if c.val < k then zext b ((j c : ℤ) - i r) else zext a ((j c : ℤ) - i r) with hM
  have hTle : T ≤ j ck + 1 := by
    rw [hT]; split_ifs <;> omega
  -- the `b`-column at `j_k`, expanded
  have hcol : (fun r => zext b ((j ck : ℤ) - i r)) =
      (∑ t ∈ range T, y ^ t • fun r => zext a ((j ck : ℤ) - t - i r)) +
        y ^ T • fun r => zext b ((j ck : ℤ) - T - i r) := by
    funext r
    rw [Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      zext_cauchyConv_geometric_iterate a y ((j ck : ℤ) - i r) T]
    congr 1
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      congr 2; ring
    · rw [smul_eq_mul]
      congr 2; ring
  have hmix : mixMinor a b i j (k + 1) =
      (M.updateCol ck fun r => zext b ((j ck : ℤ) - i r)).det := by
    unfold mixMinor
    congr 1
    ext r c
    rw [updateCol_apply]
    by_cases hc : c = ck
    · subst hc; simp [hck]
    · have hcv : c.val ≠ k := fun h => hc (Fin.ext h)
      simp only [hM, Matrix.of_apply, hc, if_false]
      by_cases hlt : c.val < k
      · rw [if_pos (by omega), if_pos hlt]
      · rw [if_neg (by omega), if_neg hlt]
  rw [hmix, hcol, det_updateCol_add, det_updateCol_finset_sum, det_updateCol_smul]
  -- the remainder column vanishes
  have hrem : (M.updateCol ck fun r => zext b ((j ck : ℤ) - T - i r)).det = 0 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · refine det_eq_zero_of_column_eq_zero ck fun r => ?_
      rw [updateCol_apply, if_pos rfl]
      have hT' : T = j ck + 1 := by rw [hT, if_pos hk0]
      rw [hT', zext_of_neg _ (by push_cast; omega)]
    · set ck' : Fin m := ⟨k - 1, by omega⟩ with hck'
      have hne : ck ≠ ck' := by
        intro h; have := congrArg Fin.val h; simp [hck, hck'] at this; omega
      have hT' : T = j ck - j ck' := by rw [hT, if_neg (by omega)]
      have hjlt : j ck' < j ck := hj (by simp [Fin.lt_def, hck, hck']; omega)
      refine det_zero_of_column_eq hne fun r => ?_
      rw [updateCol_apply, updateCol_apply, if_pos rfl, if_neg hne.symm]
      simp only [hM, Matrix.of_apply]
      rw [if_pos (show ck'.val < k by simp [hck']; omega), hT']
      congr 1
      push_cast [hjlt.le]
      ring
  rw [hrem, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun t ht => ?_
  congr 1
  have htle : t ≤ j ck := by
    have := Finset.mem_range.mp ht
    omega
  unfold mixMinor
  congr 1
  ext r c
  rw [updateCol_apply]
  by_cases hc : c = ck
  · subst hc
    have htle' : t ≤ j ⟨k, hk⟩ := htle
    simp only [if_true, Matrix.of_apply, hck, lt_irrefl, if_false, Function.update_self]
    congr 1
    rw [Nat.cast_sub htle']
    try ring
  · have hcv : c.val ≠ k := fun h => hc (Fin.ext h)
    simp only [hM, Matrix.of_apply, hc, if_false, Function.update_of_ne hc]

/-- **Branching in the mixed minors.**  For `k ≤ m`, the mixed minor with `b`-columns in the first
`k` positions is the sum over the columns interlacing `j` there. -/
theorem mixMinor_eq_sum (a : ℕ → ℝ) (y : ℝ) {m : ℕ} (i : Fin m → ℕ) :
    ∀ k, k ≤ m → ∀ j : Fin m → ℕ, StrictMono j →
      mixMinor a (cauchyConv a fun n => y ^ n) i j k =
        ∑ l ∈ interlaceSetUpTo j k, y ^ (∑ c, (j c - l c)) * toeplitzMinor a m i l := by
  classical
  intro k
  induction k with
  | zero =>
    intro _ j _
    have hset : interlaceSetUpTo j 0 = {j} := by
      ext l
      rw [mem_interlaceSetUpTo, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h2, -⟩
        exact funext fun c => h2 c (Nat.zero_le _)
      · rintro rfl
        exact ⟨fun c => le_rfl, fun c _ => rfl, fun c c' h _ => absurd h (Nat.not_lt_zero _)⟩
    rw [hset, Finset.sum_singleton, mixMinor_zero]
    simp
  | succ k ih =>
    intro hkm j hj
    have hk : k < m := hkm
    set ck : Fin m := ⟨k, hk⟩ with hck
    set T := if k = 0 then j ck + 1 else j ck - j ⟨k - 1, by omega⟩ with hT
    rw [mixMinor_succ a y i j hj hk]
    -- the updated columns stay strictly increasing
    have hupd : ∀ t ∈ range T, StrictMono (Function.update j ck (j ck - t)) := by
      intro t ht
      have htT := Finset.mem_range.mp ht
      intro c₁ c₂ h12
      by_cases h1 : c₁ = ck
      · subst h1
        rw [Function.update_self, Function.update_of_ne (ne_of_gt h12)]
        have := hj h12
        omega
      · by_cases h2 : c₂ = ck
        · subst h2
          rw [Function.update_self, Function.update_of_ne h1]
          have hk0 : k ≠ 0 := by
            intro h0; have := Fin.lt_def.mp h12; simp [hck, h0] at this
          have hT' : T = j ck - j ⟨k - 1, by omega⟩ := by rw [hT, if_neg hk0]
          have hle : j c₁ ≤ j ⟨k - 1, by omega⟩ :=
            hj.monotone (by simp [Fin.le_def]; have := Fin.lt_def.mp h12; simp [hck] at this; omega)
          have hlt : j ⟨k - 1, by omega⟩ < j ck := hj (by simp [Fin.lt_def, hck]; omega)
          omega
        · rw [Function.update_of_ne h1, Function.update_of_ne h2]
          exact hj h12
    rw [Finset.sum_congr rfl fun t ht => by
      rw [ih (by omega) _ (hupd t ht), Finset.mul_sum]]
    -- reindex the double sum
    have hset : interlaceSetUpTo j (k + 1) =
        (range T).biUnion fun t => interlaceSetUpTo (Function.update j ck (j ck - t)) k := by
      ext l
      rw [Finset.mem_biUnion, mem_interlaceSetUpTo]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨j ck - l ck, Finset.mem_range.mpr ?_, ?_⟩
        · rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · rw [hT, if_pos hk0]; omega
          · rw [hT, if_neg (by omega)]
            have := h3 ck ⟨k - 1, by omega⟩ (by simp [hck]) (by simp [hck]; omega)
            have := h1 ck
            omega
        · rw [mem_interlaceSetUpTo]
          refine ⟨fun c => ?_, fun c hc => ?_, fun c c' hc hcc' => ?_⟩
          · by_cases hc : c = ck
            · subst hc; rw [Function.update_self]; have := h1 ck; omega
            · rw [Function.update_of_ne hc]; exact h1 c
          · by_cases hc' : c = ck
            · subst hc'; rw [Function.update_self]; have := h1 ck; omega
            · rw [Function.update_of_ne hc']
              exact h2 c (by
                have : c.val ≠ k := fun h => hc' (Fin.ext h)
                omega)
          · have hc'ne : c' ≠ ck := by
              intro h; rw [h] at hcc'; simp [hck] at hcc'; omega
            rw [Function.update_of_ne hc'ne]
            exact h3 c c' (by omega) hcc'
      · rintro ⟨t, ht, hl⟩
        rw [mem_interlaceSetUpTo] at hl
        obtain ⟨h1, h2, h3⟩ := hl
        have htT := Finset.mem_range.mp ht
        have hlck : l ck = j ck - t := by
          have := h2 ck (by simp [hck]); rwa [Function.update_self] at this
        refine ⟨fun c => ?_, fun c hc => ?_, fun c c' hc hcc' => ?_⟩
        · by_cases hc : c = ck
          · subst hc; omega
          · have := h1 c; rwa [Function.update_of_ne hc] at this
        · have hne : c ≠ ck := by intro h; rw [h] at hc; simp [hck] at hc
          have := h2 c (by omega); rwa [Function.update_of_ne hne] at this
        · by_cases hcck : c = ck
          · subst hcck
            have hk0 : k ≠ 0 := by intro h0; simp [hck, h0] at hcc'
            have hc'v : c'.val = k - 1 := by simp [hck] at hcc'; omega
            have hjc' : j c' = j ⟨k - 1, by omega⟩ := congrArg j (Fin.ext hc'v)
            have hT' : T = j ⟨k, hk⟩ - j ⟨k - 1, by omega⟩ := by rw [hT, if_neg hk0]
            have e : j ck = j ⟨k, hk⟩ := rfl
            rw [hlck, hjc']
            omega
          · have hc'ne : c' ≠ ck := by
              intro h; rw [h] at hcc'; simp [hck] at hcc'
              have : c.val < k + 1 := hc
              have : c.val ≠ k := fun h => hcck (Fin.ext h)
              omega
            have := h3 c c' (by
              have : c.val ≠ k := fun h => hcck (Fin.ext h)
              omega) hcc'
            rwa [Function.update_of_ne hc'ne] at this
    have hdisj : ((range T : Finset ℕ) : Set ℕ).PairwiseDisjoint
        fun t => interlaceSetUpTo (Function.update j ck (j ck - t)) k := by
      intro t₁ ht₁ t₂ ht₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro l hl₁ hl₂
      rw [mem_interlaceSetUpTo] at hl₁ hl₂
      have e₁ := hl₁.2.1 ck (by simp [hck])
      have e₂ := hl₂.2.1 ck (by simp [hck])
      rw [Function.update_self] at e₁ e₂
      have h₁ := Finset.mem_range.mp (Finset.mem_coe.mp ht₁)
      have h₂ := Finset.mem_range.mp (Finset.mem_coe.mp ht₂)
      have hTle : T ≤ j ck + 1 := by rw [hT]; split_ifs <;> omega
      exact hne (by omega)
    rw [hset, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun l hl => ?_
    rw [mem_interlaceSetUpTo] at hl
    have hlck : l ck = j ck - t := by
      have := hl.2.1 ck (by simp [hck]); rwa [Function.update_self] at this
    have htle : t ≤ j ck := by
      have := Finset.mem_range.mp ht
      have hTle : T ≤ j ck + 1 := by rw [hT]; split_ifs <;> omega
      omega
    have hexp : (∑ c, (j c - l c)) = t + ∑ c, (Function.update j ck (j ck - t) c - l c) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ck),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ ck), Function.update_self, hlck,
        Nat.sub_self, zero_add, Nat.sub_sub_self htle]
      congr 1
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hc)]
    rw [hexp, pow_add]
    ring

/-- **Branching rule for Toeplitz minors.**  For `b = a ∗ (yⁿ)` and strictly increasing `j`,
`det (b_{j_c − i_r}) = Σ_{l interlacing j} y^{Σ (j_c − l_c)} det (a_{l_c − i_r})`. -/
theorem toeplitzMinor_cauchyConv_geometric (a : ℕ → ℝ) (y : ℝ) {m : ℕ} (i j : Fin m → ℕ)
    (hj : StrictMono j) :
    toeplitzMinor (cauchyConv a fun n => y ^ n) m i j =
      ∑ l ∈ interlaceSet j, y ^ (∑ c, (j c - l c)) * toeplitzMinor a m i l := by
  rw [← mixMinor_self a, mixMinor_eq_sum a y i m le_rfl j hj, interlaceSet]

end

end GaloisForLFunctions.HTGeometry
