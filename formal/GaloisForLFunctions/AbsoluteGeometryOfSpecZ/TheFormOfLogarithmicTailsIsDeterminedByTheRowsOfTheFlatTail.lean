import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnNestedWindowsTheCombFormTendsToWeilsFormOfTheStepPacket
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.WeilsFormInTheGaugeOfTheFlatTail

/-!
# The form of logarithmic tails is determined by the rows of the flat tail

The logarithmic tail of degree `k` at scale `N` is the divisor `ℓ_N^k(m) = log^k(N/m)` on
`[1, N]`; `b_N(k, l)` is Weil's bilinear form of two such tails. The flat tail is `k = 0`.

* **Scaling** (`logTailForm_succ`). `ℓ_{N+1} = ℓ_N + η_N` on `[1, N]`, `η_N = log(1 + 1/N)`, and
  a tail of positive degree vanishes at its own scale. Hence for `k, l ≥ 1`, exactly,

  `b_{N+1}(k, l) = Σ_{i ≤ k} Σ_{j ≤ l} C(k,i) C(l,j) η_N^{(k−i)+(l−j)} b_N(i, j)`.

* **The limits** (`tendsto_logTailForm_div`). `N η_N → 1`, so the increment
  `b_{N+1}(k,l) − b_N(k,l)` tends to `k β(k−1, l) + l β(k, l−1)` once the forms of lower degree
  have limits `β` per degree point; Cesàro summation gives the limit of `b_N(k,l)/N`. So the
  limits of all forms of logarithmic tails exist as soon as the pairings with the flat tail,

  `b_N(0, l) = Σ_{n ≤ N} log^l(N/n) R_N(n)`   (`logTailForm_zero_left`),

  have limits, and they obey `β(k, l) = k β(k−1, l) + l β(k, l−1)`.

* **Polynomial tails** (`tendsto_combForm_polyLogTail_div`). The form of the tail
  `Σ_k a_k ℓ_N^k` per degree point tends to `Σ_{k,l} a_k a_l β(k, l)`.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart (formBilin tailRow)

local notation "combW" => HodgeTheoryOfAFixedPart.combForm

/-! ### Polarization, congruence, support, finite sums -/

/-- Weil's form of a sum of two divisors. -/
theorem combForm_add (S : Finset ℕ) (c e : ℕ → ℝ) :
    combW S (fun n => c n + e n) = combW S c + 2 * formBilin S c e + combW S e := by
  rw [← HodgeTheoryOfAFixedPart.formBilin_self S (fun n => c n + e n), formBilin_add_left,
    formBilin_add_right, formBilin_add_right, HodgeTheoryOfAFixedPart.formBilin_self,
    HodgeTheoryOfAFixedPart.formBilin_self, formBilin_comm S e c]
  ring

theorem formBilin_congr {S : Finset ℕ} {c c' e e' : ℕ → ℝ} (hc : ∀ n ∈ S, c n = c' n)
    (he : ∀ n ∈ S, e n = e' n) : formBilin S c e = formBilin S c' e' := by
  have h1 := combForm_add S c e
  have h2 := combForm_add S c' e'
  have h3 : combW S (fun n => c n + e n) = combW S (fun n => c' n + e' n) :=
    combForm_congr fun n hn => by rw [hc n hn, he n hn]
  have h4 : combW S c = combW S c' := combForm_congr hc
  have h5 : combW S e = combW S e' := combForm_congr he
  linarith

/-- Two divisors that vanish off `W ⊆ S` pair on `S` as on `W`. -/
theorem formBilin_of_subset {S W : Finset ℕ} {c e : ℕ → ℝ} (hWS : W ⊆ S)
    (hc : ∀ n ∈ S, n ∉ W → c n = 0) (he : ∀ n ∈ S, n ∉ W → e n = 0) :
    formBilin S c e = formBilin W c e := by
  have h1 := combForm_add S c e
  have h2 := combForm_add W c e
  have h3 : combW S (fun n => c n + e n) = combW W (fun n => c n + e n) :=
    combForm_of_subset hWS fun n hn hnW => by
      show c n + e n = 0
      rw [hc n hn hnW, he n hn hnW, add_zero]
  have h4 : combW S c = combW W c := combForm_of_subset hWS hc
  have h5 : combW S e = combW W e := combForm_of_subset hWS he
  linarith

theorem formBilin_zero_left (S : Finset ℕ) (e : ℕ → ℝ) : formBilin S (fun _ => 0) e = 0 := by
  have h := formBilin_const_mul_left S 0 (fun _ => 0) e
  simpa using h

theorem formBilin_sum_left {ι : Type*} (S : Finset ℕ) (s : Finset ι) (f : ι → ℕ → ℝ)
    (e : ℕ → ℝ) :
    formBilin S (fun n => ∑ i ∈ s, f i n) e = ∑ i ∈ s, formBilin S (f i) e := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using formBilin_zero_left S e
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    exact (formBilin_add_left S (f a) (fun n => ∑ i ∈ s, f i n) e).trans (by rw [ih])

theorem formBilin_sum_right {ι : Type*} (S : Finset ℕ) (s : Finset ι) (c : ℕ → ℝ)
    (f : ι → ℕ → ℝ) :
    formBilin S c (fun n => ∑ i ∈ s, f i n) = ∑ i ∈ s, formBilin S c (f i) := by
  rw [formBilin_comm, formBilin_sum_left]
  exact Finset.sum_congr rfl fun i _ => formBilin_comm S (f i) c

/-! ### Logarithmic tails -/

/-- The logarithmic tail of degree `k` at scale `N`: `m ↦ log^k(N/m)`. -/
def logTail (k N : ℕ) (m : ℕ) : ℝ := Real.log ((N : ℝ) / m) ^ k

/-- Weil's form of two logarithmic tails on `[1, N]`. -/
def logTailForm (k l N : ℕ) : ℝ := formBilin (Icc 1 N) (logTail k N) (logTail l N)

/-- The step of the scale: `η_N = log((N + 1)/N)`. -/
def scaleStep (N : ℕ) : ℝ := Real.log (((N : ℝ) + 1) / N)

/-- **The pairing with the flat tail**: `b_N(0, l) = Σ_{n ≤ N} log^l(N/n) R_N(n)`. -/
theorem logTailForm_zero_left (l N : ℕ) :
    logTailForm 0 l N = ∑ n ∈ Icc 1 N, logTail l N n * tailRow N n := by
  have h : logTail 0 N = fun _ => 1 := funext fun m => pow_zero _
  rw [logTailForm, h]
  exact HodgeTheoryOfAFixedPart.formBilin_flatTail N (logTail l N)

theorem logTailForm_comm (k l N : ℕ) : logTailForm k l N = logTailForm l k N := by
  rw [logTailForm, logTailForm, formBilin_comm]

/-- A tail of positive degree vanishes at its own scale. -/
theorem logTail_self {k : ℕ} (hk : k ≠ 0) (N : ℕ) : logTail k N N = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [logTail, hk]
  · have h : ((N : ℝ) / N) = 1 := div_self (by exact_mod_cast hN.ne')
    rw [logTail, h, Real.log_one, zero_pow hk]

/-- Raising the scale by one shifts the logarithm by `η_N`. -/
theorem logTail_succ {k N m : ℕ} (hm : m ∈ Icc 1 N) :
    logTail k (N + 1) m =
      ∑ i ∈ range (k + 1), (scaleStep N ^ (k - i) * (k.choose i : ℝ)) * logTail i N m := by
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hm1.trans hmN)
  have hlog : Real.log (((N + 1 : ℕ) : ℝ) / m) = Real.log ((N : ℝ) / m) + scaleStep N := by
    rw [scaleStep, ← Real.log_mul (div_pos hN0 hm0).ne' (div_pos (by positivity) hN0).ne']
    congr 1
    rw [Nat.cast_succ]
    field_simp
  rw [logTail, hlog, add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logTail]
  ring

/-- **The scaling recursion.** For `k, l ≥ 1`:
`b_{N+1}(k, l) = Σ_{i ≤ k} Σ_{j ≤ l} C(k,i) C(l,j) η_N^{(k−i)+(l−j)} b_N(i, j)`. -/
theorem logTailForm_succ {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (N : ℕ) :
    logTailForm k l (N + 1) =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (l + 1),
        ((k.choose i : ℝ) * (l.choose j)) * scaleStep N ^ ((k - i) + (l - j)) *
          logTailForm i j N := by
  have hsub : Icc 1 N ⊆ Icc 1 (N + 1) := Finset.Icc_subset_Icc_right (Nat.le_succ N)
  have hzero : ∀ p : ℕ, p ≠ 0 → ∀ n ∈ Icc 1 (N + 1), n ∉ Icc 1 N →
      logTail p (N + 1) n = 0 := by
    intro p hp n hn hnW
    have h1 := Finset.mem_Icc.mp hn
    have h2 : ¬ (1 ≤ n ∧ n ≤ N) := fun h => hnW (Finset.mem_Icc.mpr h)
    have hn' : n = N + 1 := by omega
    rw [hn']
    exact logTail_self hp (N + 1)
  rw [logTailForm, formBilin_of_subset hsub (hzero k hk) (hzero l hl),
    formBilin_congr (fun n hn => logTail_succ (k := k) hn) (fun n hn => logTail_succ (k := l) hn),
    formBilin_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [formBilin_const_mul_left, formBilin_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [formBilin_const_mul_right, logTailForm, pow_add]
  ring

/-! ### The limits -/

theorem tendsto_natCast_mul_scaleStep :
    Tendsto (fun N : ℕ => (N : ℝ) * scaleStep N) atTop (𝓝 1) := by
  have h := (Real.tendsto_mul_log_one_add_div_atTop 1).comp tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [Function.comp_apply, scaleStep]
  congr 2
  field_simp

theorem tendsto_scaleStep : Tendsto scaleStep atTop (𝓝 0) := by
  have h := tendsto_natCast_mul_scaleStep.mul
    (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [Function.comp_apply]
  field_simp

/-- One term of the increment: `c η_N^p b_N → c 0^{p−1} B` when `b_N/N → B`, `p ≥ 1`. -/
theorem tendsto_mul_scaleStep_pow_mul {b : ℕ → ℝ} {B : ℝ}
    (hb : Tendsto (fun N : ℕ => b N / N) atTop (𝓝 B)) (c : ℝ) {p : ℕ} (hp : p ≠ 0) :
    Tendsto (fun N : ℕ => c * scaleStep N ^ p * b N) atTop (𝓝 (c * 0 ^ (p - 1) * B)) := by
  have h := ((tendsto_natCast_mul_scaleStep.mul (tendsto_scaleStep.pow (p - 1))).const_mul c).mul hb
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  simp only [Nat.succ_sub_one, pow_succ]
  field_simp

/-- **Cesàro.** If the increments of `u` tend to `L`, then `u_N/N → L`. -/
theorem tendsto_div_natCast_of_tendsto_succ_sub {u : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun N => u (N + 1) - u N) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => u N / N) atTop (𝓝 L) := by
  have hc := h.cesaro
  have h0 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * u 0) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).mul_const (u 0)
    simpa using this
  have hsum := hc.add h0
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  rw [Finset.sum_range_sub]
  ring

/-- **The forms of all logarithmic tails have limits per degree point as soon as the pairings
with the flat tail do**, and the limits obey `β(k, l) = k β(k−1, l) + l β(k, l−1)`. -/
theorem tendsto_logTailForm_div (β : ℕ → ℕ → ℝ)
    (hbase : ∀ l, Tendsto (fun N : ℕ => logTailForm 0 l N / N) atTop (𝓝 (β 0 l)))
    (hsymm : ∀ k, β k 0 = β 0 k)
    (hrec : ∀ k l, β (k + 1) (l + 1) = (k + 1) * β k (l + 1) + (l + 1) * β (k + 1) l) :
    ∀ k l, Tendsto (fun N : ℕ => logTailForm k l N / N) atTop (𝓝 (β k l)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hbase
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ihl =>
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · rw [hsymm]
    exact (hbase (k + 1)).congr fun N => by rw [logTailForm_comm]
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  refine tendsto_div_natCast_of_tendsto_succ_sub ?_
  -- the increment: every term of the recursion but the top one
  have hstep : ∀ N : ℕ, logTailForm (k + 1) (l + 1) (N + 1) - logTailForm (k + 1) (l + 1) N =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (l + 1 + 1),
          (((k + 1).choose i : ℝ) * ((l + 1).choose j)) *
            scaleStep N ^ ((k + 1 - i) + (l + 1 - j)) * logTailForm i j N +
        ∑ j ∈ range (l + 1),
          (((k + 1).choose (k + 1) : ℝ) * ((l + 1).choose j)) *
            scaleStep N ^ ((k + 1 - (k + 1)) + (l + 1 - j)) * logTailForm (k + 1) j N := by
    intro N
    rw [logTailForm_succ (Nat.succ_ne_zero k) (Nat.succ_ne_zero l), Finset.sum_range_succ,
      Finset.sum_range_succ _ (l + 1)]
    have htop : (((k + 1).choose (k + 1) : ℝ) * ((l + 1).choose (l + 1))) *
        scaleStep N ^ ((k + 1 - (k + 1)) + (l + 1 - (l + 1))) * logTailForm (k + 1) (l + 1) N =
        logTailForm (k + 1) (l + 1) N := by
      simp
    rw [htop]
    ring
  -- the limits of the terms
  have hlim1 : Tendsto (fun N : ℕ => ∑ i ∈ range (k + 1), ∑ j ∈ range (l + 1 + 1),
      (((k + 1).choose i : ℝ) * ((l + 1).choose j)) *
        scaleStep N ^ ((k + 1 - i) + (l + 1 - j)) * logTailForm i j N) atTop
      (𝓝 (∑ i ∈ range (k + 1), ∑ j ∈ range (l + 1 + 1),
        (((k + 1).choose i : ℝ) * ((l + 1).choose j)) *
          0 ^ ((k + 1 - i) + (l + 1 - j) - 1) * β i j)) :=
    tendsto_finsetSum _ fun i hi => tendsto_finsetSum _ fun j _ =>
      tendsto_mul_scaleStep_pow_mul (ihk i (Finset.mem_range.mp hi) j) _
        (by have := Finset.mem_range.mp hi; omega)
  have hlim2 : Tendsto (fun N : ℕ => ∑ j ∈ range (l + 1),
      (((k + 1).choose (k + 1) : ℝ) * ((l + 1).choose j)) *
        scaleStep N ^ ((k + 1 - (k + 1)) + (l + 1 - j)) * logTailForm (k + 1) j N) atTop
      (𝓝 (∑ j ∈ range (l + 1), (((k + 1).choose (k + 1) : ℝ) * ((l + 1).choose j)) *
        0 ^ ((k + 1 - (k + 1)) + (l + 1 - j) - 1) * β (k + 1) j)) :=
    tendsto_finsetSum _ fun j hj =>
      tendsto_mul_scaleStep_pow_mul (ihl j (by have := Finset.mem_range.mp hj; omega)) _
        (by have := Finset.mem_range.mp hj; omega)
  -- only the terms of total defect one survive
  have hval1 : ∑ i ∈ range (k + 1), ∑ j ∈ range (l + 1 + 1),
      (((k + 1).choose i : ℝ) * ((l + 1).choose j)) *
        0 ^ ((k + 1 - i) + (l + 1 - j) - 1) * β i j = ((k : ℝ) + 1) * β k (l + 1) := by
    rw [Finset.sum_eq_single k, Finset.sum_eq_single (l + 1)]
    · simp [Nat.choose_succ_self_right]
    · intro j hj hne
      have := Finset.mem_range.mp hj
      rw [zero_pow (by omega), mul_zero, zero_mul]
    · simp
    · intro i hi hne
      have := Finset.mem_range.mp hi
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [zero_pow (by omega), mul_zero, zero_mul]
    · simp
  have hval2 : ∑ j ∈ range (l + 1), (((k + 1).choose (k + 1) : ℝ) * ((l + 1).choose j)) *
      0 ^ ((k + 1 - (k + 1)) + (l + 1 - j) - 1) * β (k + 1) j = ((l : ℝ) + 1) * β (k + 1) l := by
    rw [Finset.sum_eq_single l]
    · simp [Nat.choose_succ_self_right]
    · intro j hj hne
      have := Finset.mem_range.mp hj
      rw [zero_pow (by omega), mul_zero, zero_mul]
    · simp
  have h := hlim1.add hlim2
  rw [hval1, hval2, ← hrec] at h
  exact h.congr fun N => (hstep N).symm

/-! ### Polynomial tails -/

/-- The tail `m ↦ Σ_{k < n} a_k log^k(N/m)`. -/
def polyLogTail (n : ℕ) (a : ℕ → ℝ) (N m : ℕ) : ℝ := ∑ k ∈ range n, a k * logTail k N m

theorem combForm_polyLogTail (n : ℕ) (a : ℕ → ℝ) (N : ℕ) :
    combW (Icc 1 N) (polyLogTail n a N) =
      ∑ k ∈ range n, ∑ l ∈ range n, a k * a l * logTailForm k l N := by
  have h : polyLogTail n a N = fun m => ∑ k ∈ range n, a k * logTail k N m := rfl
  rw [← HodgeTheoryOfAFixedPart.formBilin_self, h, formBilin_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [formBilin_const_mul_left, formBilin_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [formBilin_const_mul_right, logTailForm]
  ring

/-- **The form of a polynomial tail per degree point** tends to `Σ_{k,l} a_k a_l β(k, l)`. -/
theorem tendsto_combForm_polyLogTail_div {β : ℕ → ℕ → ℝ}
    (hβ : ∀ k l, Tendsto (fun N : ℕ => logTailForm k l N / N) atTop (𝓝 (β k l)))
    (n : ℕ) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ => combW (Icc 1 N) (polyLogTail n a N) / N) atTop
      (𝓝 (∑ k ∈ range n, ∑ l ∈ range n, a k * a l * β k l)) := by
  have h : Tendsto (fun N : ℕ => ∑ k ∈ range n, ∑ l ∈ range n,
      a k * a l * (logTailForm k l N / N)) atTop
      (𝓝 (∑ k ∈ range n, ∑ l ∈ range n, a k * a l * β k l)) :=
    tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ => (hβ k l).const_mul _
  refine h.congr fun N => ?_
  rw [combForm_polyLogTail, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun l _ => by ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
