import GaloisForLFunctions.HTGeometry.BaileyBorweinPlouffePi
import GaloisForLFunctions.HTGeometry.BinaryParityDriftExactLaws

/-!
# The parity drift of `π` through the Bailey–Crandall sequence

With `R(k) = 4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6)` the BBP formula gives
`16ⁿ π = hₙ + tₙ`, where `h₀ = R(0)`, `h_{n+1} = 16 hₙ + R(n+1)` and the tail
`tₙ = Σ_j 16^{−(j+1)} R(n+1+j)` lies in `[0, 4/(15(8n+9))]`.  The Bailey–Crandall sequence
`xₙ = fract hₙ` obeys `x_{n+1} = fract(16 xₙ + R(n+1))` and `fract(16ⁿπ) = fract(xₙ + tₙ)`.

* `drift_two_mul_eq_sum_hexWeight` : for every real `x`, `D_x(2M) = Σ_{n<M} w(hex digit n+1)`,
  where `w(h) = φ(h div 4) + φ(h mod 4)` and `φ(q) = [q = 2] − [q = 1]`.
* `tendsto_drift_pi_of_bbpEquidistributed` : if the Bailey–Crandall sequence is equidistributed
  in `[0, 1)`, then `D_π(N)/N → 0`, so the Parity-Drift Hypothesis fails.

The Parity-Drift Hypothesis for `π` is therefore a statement about the forced dynamical system
`x ↦ fract(16x + R(n))`, and its refutation needs only the equidistribution of one explicit
sequence (an instance of the Bailey–Crandall Hypothesis A).
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.BBPPi

open BinaryParityDrift

/-- The head `hₙ = Σ_{k ≤ n} 16^{n−k} R(k)` of `16ⁿ π`. -/
noncomputable def bbpHead : ℕ → ℝ
  | 0 => bbpTerm 0
  | n + 1 => 16 * bbpHead n + bbpTerm (n + 1)

/-- The Bailey–Crandall sequence `xₙ = fract hₙ`. -/
noncomputable def bbpSeq (n : ℕ) : ℝ := Int.fract (bbpHead n)

/-- The tail `tₙ = Σ_j 16^{−(j+1)} R(n+1+j)`. -/
noncomputable def bbpTail (n : ℕ) : ℝ := ∑' j : ℕ, (1 / 16 : ℝ) ^ (j + 1) * bbpTerm (n + 1 + j)

theorem sum_range_bbp (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 / 16 : ℝ) ^ k * bbpTerm k = bbpHead n / 16 ^ n := by
  induction n with
  | zero => simp [bbpHead]
  | succ n ih =>
    rw [sum_range_succ, ih, bbpHead, one_div_pow]
    field_simp
    ring

theorem summable_bbpTail (n : ℕ) :
    Summable fun j : ℕ => (1 / 16 : ℝ) ^ (j + 1) * bbpTerm (n + 1 + j) := by
  have h := (summable_nat_add_iff (n + 1)).mpr summable_bbp
  refine (h.mul_left (16 ^ (n + 1) * (1 / 16))).congr fun j => ?_
  rw [show j + (n + 1) = n + 1 + j by ring]
  simp only [one_div, inv_pow]
  field_simp
  ring

/-- **`16ⁿ π = hₙ + tₙ`.** -/
theorem sixteen_pow_mul_pi (n : ℕ) : (16 : ℝ) ^ n * Real.pi = bbpHead n + bbpTail n := by
  have hsplit := summable_bbp.sum_add_tsum_nat_add (n + 1)
  rw [hasSum_bbp.tsum_eq, sum_range_bbp] at hsplit
  rw [← hsplit, mul_add, mul_div_cancel₀ _ (by positivity : (16 : ℝ) ^ n ≠ 0), ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show j + (n + 1) = n + 1 + j by ring]
  simp only [one_div, inv_pow]
  field_simp
  ring

theorem bbpTail_nonneg (n : ℕ) : 0 ≤ bbpTail n :=
  tsum_nonneg fun j => mul_nonneg (by positivity) (bbpTerm_nonneg _)

theorem bbpTail_le (n : ℕ) : bbpTail n ≤ 4 / (8 * n + 9) / 15 := by
  have hb : ∀ j : ℕ, (1 / 16 : ℝ) ^ (j + 1) * bbpTerm (n + 1 + j) ≤
      4 / (8 * n + 9) * ((1 / 16) * (1 / 16) ^ j) := fun j => by
    have h1 := bbpTerm_le (n + 1 + j)
    have h2 : (4 : ℝ) / (8 * ((n + 1 + j : ℕ) : ℝ) + 1) ≤ 4 / (8 * n + 9) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      push_cast; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have h3 : (0 : ℝ) ≤ (1 / 16) ^ (j + 1) := by positivity
    calc (1 / 16 : ℝ) ^ (j + 1) * bbpTerm (n + 1 + j) ≤ (1 / 16) ^ (j + 1) * (4 / (8 * n + 9)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) h3
      _ = _ := by rw [pow_succ]; ring
  have hg : Summable fun j : ℕ => 4 / (8 * (n : ℝ) + 9) * ((1 / 16) * (1 / 16) ^ j) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _).mul_left _
  calc bbpTail n ≤ ∑' j : ℕ, 4 / (8 * (n : ℝ) + 9) * ((1 / 16) * (1 / 16) ^ j) :=
        Summable.tsum_le_tsum hb (summable_bbpTail n) hg
    _ = 4 / (8 * n + 9) / 15 := by
        rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
        ring

theorem tendsto_bbpTail : Tendsto bbpTail atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 4 / (8 * (n : ℝ) + 9) / 15) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => 8 * (n : ℝ) + 9) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    have h' := (this.inv_tendsto_atTop.const_mul 4).div_const 15
    rw [mul_zero, zero_div] at h'
    exact h'.congr fun n => by simp only [Pi.inv_apply]; ring
  exact squeeze_zero bbpTail_nonneg bbpTail_le h

/-- **The Bailey–Crandall recursion** `x_{n+1} = fract(16 xₙ + R(n+1))`. -/
theorem bbpSeq_succ (n : ℕ) : bbpSeq (n + 1) = Int.fract (16 * bbpSeq n + bbpTerm (n + 1)) := by
  unfold bbpSeq
  rw [bbpHead, ← Int.self_sub_floor (bbpHead n)]
  rw [show 16 * (bbpHead n - ⌊bbpHead n⌋) + bbpTerm (n + 1) =
      16 * bbpHead n + bbpTerm (n + 1) - ((16 * ⌊bbpHead n⌋ : ℤ) : ℝ) by push_cast; ring,
    Int.fract_sub_intCast]

theorem fract_sixteen_pow_mul_pi (n : ℕ) :
    Int.fract ((16 : ℝ) ^ n * Real.pi) = Int.fract (bbpSeq n + bbpTail n) := by
  rw [sixteen_pow_mul_pi, bbpSeq, ← Int.self_sub_floor (bbpHead n),
    show bbpHead n - ⌊bbpHead n⌋ + bbpTail n = bbpHead n + bbpTail n - (⌊bbpHead n⌋ : ℝ) by ring,
    Int.fract_sub_intCast]

/-! ### Hexadecimal digits and the parity drift -/

/-- `φ(q) = [q = 2] − [q = 1]`. -/
def quatWeight (q : ℤ) : ℤ := (if q = 2 then 1 else 0) - (if q = 1 then 1 else 0)

/-- `w(h) = φ(h div 4) + φ(h mod 4)`. -/
def hexWeight (h : ℤ) : ℤ := quatWeight (h / 4) + quatWeight (h % 4)

theorem abs_hexWeight_le (h : ℤ) : |hexWeight h| ≤ 2 := by
  unfold hexWeight quatWeight
  rw [abs_le]
  constructor <;> split_ifs <;> omega

theorem floor_sixteen_pow_succ (x : ℝ) (n : ℕ) :
    ⌊(16 : ℝ) ^ (n + 1) * x⌋ =
      16 * ⌊(16 : ℝ) ^ n * x⌋ + (4 * quatDigit x (2 * n + 1) + quatDigit x (2 * n + 2)) := by
  have e1 := floor_four_pow_succ x (2 * n + 1)
  have e0 := floor_four_pow_succ x (2 * n)
  have q1 := quatDigit_succ x (2 * n)
  have q2 := quatDigit_succ x (2 * n + 1)
  have h16 : ∀ m : ℕ, (16 : ℝ) ^ m = (4 : ℝ) ^ (2 * m) := fun m => by rw [pow_mul]; norm_num
  rw [h16, h16, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, e1, e0, q1,
    show 2 * n + 1 + 1 = 2 * n + 2 by ring, q2,
    show 2 * (2 * n + 1) + 1 = 2 * (2 * n + 1) + 1 from rfl]
  ring_nf

theorem floor_sixteen_mul_fract (x : ℝ) (n : ℕ) :
    ⌊16 * Int.fract ((16 : ℝ) ^ n * x)⌋ =
      4 * quatDigit x (2 * n + 1) + quatDigit x (2 * n + 2) := by
  have h := floor_sixteen_pow_succ x n
  rw [pow_succ, show (16 : ℝ) ^ n * 16 * x = 16 * Int.fract ((16 : ℝ) ^ n * x) +
      ((16 * ⌊(16 : ℝ) ^ n * x⌋ : ℤ) : ℝ) by push_cast; rw [Int.fract]; ring,
    Int.floor_add_intCast] at h
  linarith

theorem quatDigit_nonneg (x : ℝ) (m : ℕ) : 0 ≤ quatDigit x m := Int.emod_nonneg _ (by norm_num)

theorem quatDigit_lt_four (x : ℝ) (m : ℕ) : quatDigit x m < 4 := Int.emod_lt_of_pos _ (by norm_num)

/-- **Hexadecimal form of the drift.**  `D_x(2M) = Σ_{n<M} w(⌊16 fract(16ⁿ x)⌋)`. -/
theorem drift_two_mul_eq_sum_hexWeight (x : ℝ) (M : ℕ) :
    drift x (2 * M) = ∑ n ∈ range M, hexWeight ⌊16 * Int.fract ((16 : ℝ) ^ n * x)⌋ := by
  induction M with
  | zero => simp [drift]
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, drift, sum_range_succ, sum_range_succ, ← drift,
      ih, sum_range_succ, floor_sixteen_mul_fract, binDigit_sub_binDigit_eq,
      binDigit_sub_binDigit_eq]
    have a0 := quatDigit_nonneg x (2 * M + 1)
    have a1 := quatDigit_lt_four x (2 * M + 1)
    have b0 := quatDigit_nonneg x (2 * M + 2)
    have b1 := quatDigit_lt_four x (2 * M + 2)
    have e1 : 4 * quatDigit x (2 * M + 1) + quatDigit x (2 * M + 2) =
        4 * quatDigit x (2 * M + 1) + quatDigit x (2 * M + 2) := rfl
    rw [show 2 * M + 1 + 1 = 2 * M + 2 by ring]
    unfold hexWeight quatWeight
    have hdiv : (4 * quatDigit x (2 * M + 1) + quatDigit x (2 * M + 2)) / 4 =
        quatDigit x (2 * M + 1) := by omega
    have hmod : (4 * quatDigit x (2 * M + 1) + quatDigit x (2 * M + 2)) % 4 =
        quatDigit x (2 * M + 2) := by omega
    rw [hdiv, hmod]
    ring

/-! ### Equidistribution of the Bailey–Crandall sequence refutes the hypothesis -/

/-- The Bailey–Crandall sequence is equidistributed in `[0, 1)`. -/
def BBPEquidistributed : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun M : ℕ => (#{n ∈ range M | bbpSeq n ∈ Set.Ico a b} : ℝ) / M) atTop (𝓝 (b - a))

theorem sum_hexWeight_range : ∑ h ∈ range 16, hexWeight (h : ℤ) = 0 := by decide

theorem bbpSeq_mem (n : ℕ) : 0 ≤ bbpSeq n ∧ bbpSeq n < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The hex digit of `xₙ` as a sum over the sixteen cells. -/
theorem hexWeight_floor_eq_sum (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (hexWeight ⌊16 * z⌋ : ℝ) =
      ∑ h ∈ range 16,
        (hexWeight h : ℝ) * (if z ∈ Set.Ico ((h : ℝ) / 16) ((h + 1) / 16) then 1 else 0) := by
  have hf0 : 0 ≤ ⌊16 * z⌋ := Int.floor_nonneg.mpr (by linarith)
  have hf1 : ⌊16 * z⌋ < 16 := Int.floor_lt.mpr (by push_cast; linarith)
  set h0 := (⌊16 * z⌋).toNat with hh0
  have hcast : ((h0 : ℕ) : ℤ) = ⌊16 * z⌋ := Int.toNat_of_nonneg hf0
  have hmem : h0 ∈ range 16 := mem_range.mpr (by omega)
  have hiff : ∀ h : ℕ, z ∈ Set.Ico ((h : ℝ) / 16) ((h + 1) / 16) ↔ h = h0 := by
    intro h
    rw [Set.mem_Ico, div_le_iff₀ (by norm_num), lt_div_iff₀ (by norm_num)]
    constructor
    · rintro ⟨h1, h2⟩
      have : ⌊16 * z⌋ = (h : ℤ) := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      omega
    · rintro rfl
      have hl := Int.floor_le (16 * z)
      have hu := Int.lt_floor_add_one (16 * z)
      rw [← hcast] at hl hu
      push_cast at hl hu
      constructor <;> linarith
  rw [sum_eq_single h0]
  · rw [if_pos ((hiff h0).mpr rfl), mul_one, ← hcast]
  · intro h _ hne
    rw [if_neg (fun hm => hne ((hiff h).mp hm)), mul_zero]
  · intro h; exact absurd hmem h

theorem tendsto_sum_hexWeight_bbpSeq (hE : BBPEquidistributed) :
    Tendsto (fun M : ℕ => (∑ n ∈ range M, (hexWeight ⌊16 * bbpSeq n⌋ : ℝ)) / M) atTop (𝓝 0) := by
  have hcell : ∀ h ∈ range 16, Tendsto (fun M : ℕ => (hexWeight h : ℝ) *
      ((#{n ∈ range M | bbpSeq n ∈ Set.Ico ((h : ℝ) / 16) ((h + 1) / 16)} : ℝ) / M)) atTop
      (𝓝 ((hexWeight h : ℝ) * (1 / 16))) := by
    intro h hh
    have hh' : (h : ℝ) ≤ 15 := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hh)
    have := (hE ((h : ℝ) / 16) ((h + 1) / 16) (by positivity) (by linarith)
      (by rw [div_le_one (by norm_num)]; linarith)).const_mul (hexWeight h : ℝ)
    convert this using 2
    ring
  have hsum := tendsto_finsetSum (range 16) hcell
  have hzero : ∑ h ∈ range 16, (hexWeight h : ℝ) * (1 / 16) = 0 := by
    rw [← sum_mul]
    have := congrArg (fun z : ℤ => (z : ℝ)) sum_hexWeight_range
    push_cast at this
    rw [this, zero_mul]
  rw [hzero] at hsum
  refine hsum.congr fun M => ?_
  rw [sum_congr rfl fun n _ => hexWeight_floor_eq_sum _ (bbpSeq_mem n).1 (bbpSeq_mem n).2, sum_comm,
    sum_div]
  refine sum_congr rfl fun h _ => ?_
  rw [← mul_sum, sum_boole, mul_div_assoc]

/-- If `0 ≤ x < 1`, `0 ≤ t ≤ ε` and `x` is more than `ε` below the next sixteenth, then `x + t`
has the same first hexadecimal digit as `x`. -/
theorem floor_sixteen_fract_add_eq {x t ε : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (ht0 : 0 ≤ t)
    (htε : t ≤ ε) (hgood : x + ε < ((⌊16 * x⌋ : ℝ) + 1) / 16) :
    ⌊16 * Int.fract (x + t)⌋ = ⌊16 * x⌋ := by
  have hf := Int.floor_le (16 * x)
  have hf15 : ⌊16 * x⌋ ≤ 15 := by
    have : ⌊16 * x⌋ < 16 := Int.floor_lt.mpr (by push_cast; linarith)
    omega
  have hf15' : (⌊16 * x⌋ : ℝ) ≤ 15 := by exact_mod_cast hf15
  have hfr : Int.fract (x + t) = x + t := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [hfr, Int.floor_eq_iff]
  constructor <;> linarith

/-- A point that fails the margin condition lies in one of sixteen short cells. -/
theorem mem_bad_of_not_good {x ε : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hbad : ¬ x + ε < ((⌊16 * x⌋ : ℝ) + 1) / 16) :
    ∃ h ∈ range 16, x ∈ Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16) := by
  have hf0 : 0 ≤ ⌊16 * x⌋ := Int.floor_nonneg.mpr (by linarith)
  have hf1 : ⌊16 * x⌋ < 16 := Int.floor_lt.mpr (by push_cast; linarith)
  refine ⟨(⌊16 * x⌋).toNat, mem_range.mpr (by omega), ?_⟩
  have hc : (((⌊16 * x⌋).toNat : ℕ) : ℝ) = (⌊16 * x⌋ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hf0
  rw [hc]
  have hu := Int.lt_floor_add_one (16 * x)
  constructor <;> linarith

/-- **Equidistribution of the Bailey–Crandall sequence refutes the Parity-Drift Hypothesis.** -/
theorem tendsto_drift_pi_of_bbpEquidistributed (hE : BBPEquidistributed) :
    Tendsto (fun N : ℕ => (drift Real.pi N : ℝ) / N) atTop (𝓝 0) := by
  set Hx : ℕ → ℤ := fun n => ⌊16 * bbpSeq n⌋ with hHx
  set Hy : ℕ → ℤ := fun n => ⌊16 * Int.fract ((16 : ℝ) ^ n * Real.pi)⌋ with hHy
  have hS := tendsto_sum_hexWeight_bbpSeq hE
  -- the even-length drift is `o(M)`
  have heven : ∀ η > 0, ∀ᶠ M : ℕ in atTop, |(drift Real.pi (2 * M) : ℝ)| ≤ η * M := by
    intro η hη
    set ε : ℝ := min (1 / 16) (η / 256) with hεdef
    have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε ≤ 1 / 16 := min_le_left _ _
    have hε2 : ε ≤ η / 256 := min_le_right _ _
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (tendsto_bbpTail.eventually (ge_mem_nhds hε0))
    -- frequencies of the sixteen short cells
    have hcells : ∀ h ∈ range 16, Tendsto (fun M : ℕ =>
        (#{n ∈ range M | bbpSeq n ∈ Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)} : ℝ) / M)
        atTop (𝓝 ε) := by
      intro h hh
      have hh' : (h : ℝ) ≤ 15 := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hh)
      have := hE (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)
        (by have : (0 : ℝ) ≤ h := Nat.cast_nonneg h; linarith) (by linarith)
        (by rw [div_le_one (by norm_num)]; linarith)
      rwa [sub_sub_cancel] at this
    have hU : Tendsto (fun M : ℕ => |(∑ n ∈ range M, (hexWeight (Hx n) : ℝ))| / M +
        4 * n₀ * (1 / (M : ℝ)) + 4 * ∑ h ∈ range 16,
          (#{n ∈ range M | bbpSeq n ∈ Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)} : ℝ) /
            M) atTop (𝓝 (0 + 4 * n₀ * 0 + 4 * ∑ _h ∈ range 16, ε)) := by
      refine ((?_ : Tendsto _ _ _).add (tendsto_one_div_atTop_nhds_zero_nat.const_mul _)).add
        ((tendsto_finsetSum _ hcells).const_mul 4)
      have := hS.abs
      rw [abs_zero] at this
      refine this.congr fun M => ?_
      rw [abs_div, Nat.abs_cast]
    have hlim : 0 + 4 * (n₀ : ℝ) * 0 + 4 * ∑ _h ∈ range 16, ε = 64 * ε := by
      simp; ring
    rw [hlim] at hU
    have h64 : 64 * ε < η := by nlinarith
    filter_upwards [hU.eventually (gt_mem_nhds h64), eventually_gt_atTop 0] with M hM hMpos
    have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
    -- compare the true hex digits with those of the Bailey–Crandall sequence
    have hdrift := drift_two_mul_eq_sum_hexWeight Real.pi M
    have hterm : ∀ n ∈ range M, |(hexWeight (Hy n) : ℝ) - hexWeight (Hx n)| ≤
        4 * ((if n < n₀ then 1 else 0) + ∑ h ∈ range 16, (if bbpSeq n ∈
          Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16) then 1 else 0)) := by
      intro n _
      have hw : |(hexWeight (Hy n) : ℝ) - hexWeight (Hx n)| ≤ 4 := by
        have a := abs_hexWeight_le (Hy n)
        have b := abs_hexWeight_le (Hx n)
        have : |hexWeight (Hy n) - hexWeight (Hx n)| ≤ 4 :=
          (abs_sub _ _).trans (by linarith)
        exact_mod_cast this
      have hnn : (0 : ℝ) ≤ ∑ h ∈ range 16, (if bbpSeq n ∈
          Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16) then (1 : ℝ) else 0) :=
        sum_nonneg fun _ _ => by split_ifs <;> norm_num
      by_cases hn : n < n₀
      · rw [if_pos hn]; linarith
      · rw [if_neg hn]
        have ht := hn₀ n (not_lt.mp hn)
        by_cases hg : bbpSeq n + ε < ((⌊16 * bbpSeq n⌋ : ℝ) + 1) / 16
        · have heq : Hy n = Hx n := by
            simp only [hHy, hHx]
            rw [fract_sixteen_pow_mul_pi]
            exact floor_sixteen_fract_add_eq (bbpSeq_mem n).1 (bbpSeq_mem n).2 (bbpTail_nonneg n)
              ht hg
          rw [heq, sub_self, abs_zero]
          positivity
        · obtain ⟨h, hh, hmem⟩ := mem_bad_of_not_good (bbpSeq_mem n).1 (bbpSeq_mem n).2 hg
          have hone : (1 : ℝ) ≤ ∑ h ∈ range 16, (if bbpSeq n ∈
              Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16) then (1 : ℝ) else 0) := by
            calc (1 : ℝ) = if bbpSeq n ∈ Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)
                  then 1 else 0 := by rw [if_pos hmem]
              _ ≤ _ := single_le_sum (f := fun h : ℕ => if bbpSeq n ∈
                  Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16) then (1 : ℝ) else 0)
                  (fun _ _ => by split_ifs <;> norm_num) hh
          linarith
    have hsumdiff : |(drift Real.pi (2 * M) : ℝ) - ∑ n ∈ range M, (hexWeight (Hx n) : ℝ)| ≤
        4 * n₀ + 4 * ∑ h ∈ range 16,
          (#{n ∈ range M | bbpSeq n ∈
            Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)} : ℝ) := by
      rw [hdrift]
      push_cast
      rw [← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
      rw [← mul_sum, sum_add_distrib, sum_comm, mul_add]
      have h1 : ∑ n ∈ range M, (if n < n₀ then (1 : ℝ) else 0) ≤ n₀ := by
        rw [sum_boole]
        have : #{n ∈ range M | n < n₀} ≤ n₀ := by
          calc #{n ∈ range M | n < n₀} ≤ #(range n₀) := card_le_card fun n hn => by
                simp only [mem_filter, mem_range] at hn ⊢; exact hn.2
            _ = n₀ := card_range n₀
        exact_mod_cast this
      have h2 : ∀ h ∈ range 16, ∑ n ∈ range M, (if bbpSeq n ∈
          Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16) then (1 : ℝ) else 0) =
          (#{n ∈ range M | bbpSeq n ∈ Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)} : ℝ) :=
        fun h _ => sum_boole _ _
      rw [sum_congr rfl h2]
      linarith
    have hmain : |(drift Real.pi (2 * M) : ℝ)| / M ≤
        |(∑ n ∈ range M, (hexWeight (Hx n) : ℝ))| / M + 4 * n₀ * (1 / (M : ℝ)) + 4 * ∑ h ∈ range 16,
          (#{n ∈ range M | bbpSeq n ∈ Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)} : ℝ) /
            M := by
      have hle : |(drift Real.pi (2 * M) : ℝ)| ≤ |(∑ n ∈ range M, (hexWeight (Hx n) : ℝ))| +
          (4 * n₀ + 4 * ∑ h ∈ range 16, (#{n ∈ range M | bbpSeq n ∈
            Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)} : ℝ)) := by
        have := abs_sub_abs_le_abs_sub (drift Real.pi (2 * M) : ℝ)
          (∑ n ∈ range M, (hexWeight (Hx n) : ℝ))
        linarith
      have hsd : ∑ h ∈ range 16, (#{n ∈ range M | bbpSeq n ∈
            Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)} : ℝ) / M =
          (∑ h ∈ range 16, (#{n ∈ range M | bbpSeq n ∈
            Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)} : ℝ)) / M := (sum_div _ _ _).symm
      rw [hsd]
      calc |(drift Real.pi (2 * M) : ℝ)| / M ≤ (|(∑ n ∈ range M, (hexWeight (Hx n) : ℝ))| +
          (4 * n₀ + 4 * ∑ h ∈ range 16, (#{n ∈ range M | bbpSeq n ∈
            Set.Ico (((h : ℝ) + 1) / 16 - ε) (((h : ℝ) + 1) / 16)} : ℝ))) / M :=
            div_le_div_of_nonneg_right hle hMr.le
        _ = _ := by field_simp; ring
    have := lt_of_le_of_lt hmain hM
    rw [div_lt_iff₀ hMr] at this
    linarith
  -- pass from even lengths to all lengths
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [(Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).eventually
      (heven (η / 2) (by positivity)), eventually_gt_atTop (⌈2 / η⌉₊)] with N hN hN'
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hN'
    exact_mod_cast this
  have hNη : 2 / η < N := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN')
  have hsplit : drift Real.pi N = drift Real.pi (2 * (N / 2)) +
      (if N % 2 = 1 then
        binDigit Real.pi (2 * (2 * (N / 2)) + 1) - binDigit Real.pi (2 * (2 * (N / 2)) + 2)
        else 0) := by
    rcases Nat.even_or_odd' N with ⟨k, hk | hk⟩
    · have h1 : N / 2 = k := by omega
      rw [h1, if_neg (by omega), add_zero, hk]
    · have h1 : N / 2 = k := by omega
      rw [h1, if_pos (by omega), hk, drift, sum_range_succ, ← drift]
  have hlast : |((if N % 2 = 1 then binDigit Real.pi (2 * (2 * (N / 2)) + 1) -
      binDigit Real.pi (2 * (2 * (N / 2)) + 2) else 0 : ℤ) : ℝ)| ≤ 1 := by
    split_ifs
    · exact abs_binDigit_sub_le _ _ _
    · simp
  rw [Real.dist_eq, sub_zero, abs_div, Nat.abs_cast, div_lt_iff₀ hNpos, hsplit]
  push_cast
  have hhalf : ((N / 2 : ℕ) : ℝ) ≤ N / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (N / 2) * 2 ≤ N := Nat.div_mul_le_self N 2
    exact_mod_cast this
  have h1 := abs_add_le ((drift Real.pi (2 * (N / 2)) : ℝ))
    ((if N % 2 = 1 then
      binDigit Real.pi (2 * (2 * (N / 2)) + 1) - binDigit Real.pi (2 * (2 * (N / 2)) + 2)
      else 0 : ℤ) : ℝ)
  push_cast at hlast h1
  have hηN : 2 < η * N := by rwa [div_lt_iff₀ hη, mul_comm] at hNη
  nlinarith

/-- **Hypothesis A for the BBP sequence of `π` refutes the Parity-Drift Hypothesis.** -/
theorem not_parityDriftHypothesis_pi_of_bbpEquidistributed (hE : BBPEquidistributed) :
    ¬ ParityDriftHypothesis Real.pi :=
  fun h => h (tendsto_drift_pi_of_bbpEquidistributed hE)

end GaloisForLFunctions.HTGeometry.BBPPi
