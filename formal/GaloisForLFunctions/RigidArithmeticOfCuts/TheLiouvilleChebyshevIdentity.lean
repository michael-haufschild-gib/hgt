import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.WhereTheFactorOfTwoGoes
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries
import GaloisForLFunctions.RigidArithmeticOfCuts.TheSelbergLedgerSeparatesTheTwin

/-!
# The Liouville–Chebyshev identity

Chebyshev's identity reads `ψ` through floors: `Σ_k ψ(x/k) = log⌊x⌋!`. The Liouville summatory function
`L(x) = Σ_{n≤x} λ(n)` has its own: since `λ ∗ 1` is the indicator of the squares,

`Σ_{k≤x} L(⌊x/k⌋) = ⌊√x⌋`.

So a stencil read against `L` has an **exact value**:
`Σ_{n≤x} h(n) L(⌊x/n⌋) = Σ_k c(k) ⌊√(x/k)⌋`, of size `√x`. This is a parity ledger with no unknown in it. Its
symbol is `D_c(s) ζ(2s)`, holomorphic right of `½`: an exact parity ledger is blind too. And since `L` has no sign,
unlike `ψ`, this identity yields no Chebyshev bound.

The term that pays the factor `2` of sieve parity is different. It is `P_c(x) = Σ_k c(k) λ(k) L(⌊x/k⌋) = Σ_{n≤x} λ(n) h(n)`.
It is bounded by the Mertens level: `L(x) = Σ_{d≤√x} M(⌊x/d²⌋)`, so `|M(y)| ≤ η y` gives
`|P_c(x)| ≤ 2 η (Σ |c(k)|/k) x`.
-/

open Finset
open ArithmeticFunction (moebius)
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The floor sum `Σ_{k≤x} U(⌊x/k⌋)`, the reading of `U` through the cut system. -/
def floorSum (U : ℕ → ℝ) (x : ℕ) : ℝ := ∑ k ∈ Ioc 0 x, U (x / k)

/-- **Floor sums are injective.** The equation `Σ_{k≤x} U(x/k) = f(x)` is triangular in `x`. -/
theorem eq_of_floorSum_eq {U V : ℕ → ℝ} (hU : U 0 = 0) (hV : V 0 = 0)
    (h : ∀ x, floorSum U x = floorSum V x) (x : ℕ) : U x = V x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [hU, hV]
    · have hsplit : ∀ W : ℕ → ℝ, floorSum W x = W x + ∑ k ∈ Ioc 1 x, W (x / k) := by
        intro W
        have hmem : Ioc 0 x = insert 1 (Ioc 1 x) := by
          ext k
          simp only [mem_Ioc, mem_insert]
          omega
        rw [floorSum, hmem, sum_insert (by simp), Nat.div_one]
      have hx' := h x
      rw [hsplit U, hsplit V] at hx'
      have hrest : ∑ k ∈ Ioc 1 x, U (x / k) = ∑ k ∈ Ioc 1 x, V (x / k) :=
        sum_congr rfl fun k hk => by
          obtain ⟨h1, -⟩ := mem_Ioc.mp hk
          exact ih _ (Nat.div_lt_self hx h1)
      linarith

/-! ### The Liouville sum through floors -/

/-- The Liouville sum as a real number. -/
def liouvilleR (N : ℕ) : ℝ := ∑ j ∈ Ioc 0 N, (ArithmeticFunction.liouville j : ℝ)

theorem liouvilleR_eq (N : ℕ) : liouvilleR N = (liouvilleSum N : ℝ) := by
  rw [liouvilleR, liouvilleSum, Int.cast_sum]
  rfl

theorem sum_divisors_liouville {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.liouville d : ℝ) = if IsSquare n then 1 else 0 := by
  have h := RHTower.sum_divisors_liouvilleC hn
  have hc : ((∑ d ∈ n.divisors, (ArithmeticFunction.liouville d : ℝ) : ℝ) : ℂ) =
      ((if IsSquare n then 1 else 0 : ℝ) : ℂ) := by
    push_cast
    simp only [RHTower.liouvilleC_apply, RHTower.squareIndicator] at h
    rw [h]
    split_ifs <;> simp
  exact_mod_cast hc

/-- The number of squares up to `x`. -/
theorem sum_Ioc_isSquare (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (if IsSquare n then (1 : ℝ) else 0) = (Nat.sqrt x : ℝ) := by
  classical
  have himage : (Ioc 0 x).filter IsSquare = (Ioc 0 (Nat.sqrt x)).image fun j => j * j := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨h0, hx⟩, j, rfl⟩
      have hj : 0 < j := Nat.pos_of_mul_pos_left h0
      exact ⟨j, ⟨hj, Nat.le_sqrt.mpr hx⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hle⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hj hj, Nat.le_sqrt.mp hle⟩, j, rfl⟩
  have hinj : Set.InjOn (fun j : ℕ => j * j) (Ioc 0 (Nat.sqrt x) : Finset ℕ) := by
    intro a _ b _ hab
    exact Nat.mul_self_inj.mp hab
  rw [← sum_filter, sum_const, himage, card_image_of_injOn hinj, nsmul_eq_mul, mul_one]
  simp

/-- **The Liouville–Chebyshev identity.** `Σ_{k≤x} L(⌊x/k⌋) = ⌊√x⌋`. -/
theorem floorSum_liouvilleR (x : ℕ) : floorSum liouvilleR x = (Nat.sqrt x : ℝ) := by
  have h := sum_Ioc_sum_divisors (fun d _ => (ArithmeticFunction.liouville d : ℝ)) x
  rw [floorSum, ← sum_Ioc_isSquare]
  have hL : ∀ e, liouvilleR (x / e) = ∑ d ∈ Ioc 0 (x / e), (ArithmeticFunction.liouville d : ℝ) :=
    fun e => rfl
  simp only [hL]
  rw [← h]
  exact sum_congr rfl fun n hn =>
    sum_divisors_liouville (Nat.pos_iff_ne_zero.mp (mem_Ioc.mp hn).1)

private lemma sum_Ioc_dvd (f : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (if k ∣ n then f n else 0) = ∑ t ∈ Ioc 0 (x / k), f (k * t) := by
  rw [← sum_filter]
  refine sum_bij' (fun n _ => n / k) (fun t _ => k * t) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hI, hd⟩ := mem_filter.mp hn
    obtain ⟨h0, hx⟩ := mem_Ioc.mp hI
    exact mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd h0 hd) hk, Nat.div_le_div_right hx⟩
  · intro t ht
    obtain ⟨h0, hx⟩ := mem_Ioc.mp ht
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos hk h0, ?_⟩, dvd_mul_right k t⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hk).mp hx
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2
  · intro t _
    exact Nat.mul_div_cancel_left t hk
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

/-- **The exact parity ledger.** A stencil read against `L` has the value `Σ_k c(k) ⌊√(x/k)⌋`, with no unknown. -/
theorem sum_increment_mul_liouvilleR {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (increment c n : ℝ) * liouvilleR (x / n) =
      ∑ k ∈ c.support, (c k : ℝ) * (Nat.sqrt (x / k) : ℝ) := by
  have hinc : ∀ n, (increment c n : ℝ) = ∑ k ∈ c.support, if k ∣ n then (c k : ℝ) else 0 := by
    intro n
    rw [increment]
    push_cast
    exact sum_congr rfl fun k _ => by split_ifs <;> simp
  simp_rw [hinc, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h
    exact Finsupp.mem_support_iff.mp hk hc0
  have hterm : ∀ n, (if k ∣ n then (c k : ℝ) else 0) * liouvilleR (x / n) =
      if k ∣ n then (c k : ℝ) * liouvilleR (x / n) else 0 := fun n => by
    split_ifs <;> simp
  simp_rw [hterm]
  rw [sum_Ioc_dvd (fun n => (c k : ℝ) * liouvilleR (x / n)) hk0, ← mul_sum,
    ← floorSum_liouvilleR (x / k), floorSum]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  rw [Nat.div_div_eq_div_mul]

/-! ### The Mertens level -/

/-- The Mertens function as a real number. -/
def mertensR (N : ℕ) : ℝ := ∑ j ∈ Ioc 0 N, (moebius j : ℝ)

theorem floorSum_mertensR {x : ℕ} (hx : 1 ≤ x) : floorSum mertensR x = 1 := by
  have h := sum_Ioc_sum_divisors (fun d _ => (moebius d : ℝ)) x
  have hM : ∀ e, mertensR (x / e) = ∑ d ∈ Ioc 0 (x / e), (moebius d : ℝ) := fun e => rfl
  rw [floorSum]
  simp only [hM]
  rw [← h]
  have hdiv : ∀ n ∈ Ioc 0 x, ∑ d ∈ n.divisors, (moebius d : ℝ) = if n = 1 then 1 else 0 := by
    intro n hn
    have h0 := (mem_Ioc.mp hn).1
    have h1 := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h1
    have h2 : ((∑ d ∈ n.divisors, moebius d : ℤ) : ℝ) = ((if n = 1 then 1 else 0 : ℤ) : ℝ) := by
      rw [h1]
    push_cast at h2
    exact h2
  rw [sum_congr rfl hdiv, sum_ite_eq' (Ioc 0 x) 1, if_pos (mem_Ioc.mpr ⟨one_pos, hx⟩)]

/-- The right side of the identity `L(x) = Σ_{d≤√x} M(x/d²)`. -/
def squareMertens (x : ℕ) : ℝ := ∑ d ∈ Ioc 0 (Nat.sqrt x), mertensR (x / (d * d))

theorem floorSum_squareMertens (x : ℕ) : floorSum squareMertens x = (Nat.sqrt x : ℝ) := by
  rw [floorSum]
  simp only [squareMertens]
  have hswap : ∑ k ∈ Ioc 0 x, ∑ d ∈ Ioc 0 (Nat.sqrt (x / k)), mertensR (x / k / (d * d)) =
      ∑ d ∈ Ioc 0 (Nat.sqrt x), ∑ k ∈ Ioc 0 (x / (d * d)), mertensR (x / k / (d * d)) := by
    refine sum_comm' fun k d => ?_
    simp only [mem_Ioc]
    constructor
    · rintro ⟨⟨hk0, hkx⟩, hd0, hd⟩
      have h1 : d * d ≤ x / k := Nat.le_sqrt.mp hd
      have h2 : d * d * k ≤ x := (Nat.le_div_iff_mul_le hk0).mp h1
      refine ⟨⟨hk0, (Nat.le_div_iff_mul_le (Nat.mul_pos hd0 hd0)).mpr (by rwa [mul_comm])⟩, hd0,
        Nat.le_sqrt.mpr ?_⟩
      exact (Nat.le_mul_of_pos_right _ hk0).trans h2
    · rintro ⟨⟨hk0, hk⟩, hd0, hd⟩
      have h1 : k * (d * d) ≤ x := (Nat.le_div_iff_mul_le (Nat.mul_pos hd0 hd0)).mp hk
      have h2 : k ≤ x := (Nat.le_mul_of_pos_right _ (Nat.mul_pos hd0 hd0)).trans h1
      refine ⟨⟨hk0, h2⟩, hd0, Nat.le_sqrt.mpr ?_⟩
      exact (Nat.le_div_iff_mul_le hk0).mpr (by rwa [mul_comm])
  rw [hswap]
  have hinner : ∀ d ∈ Ioc 0 (Nat.sqrt x),
      ∑ k ∈ Ioc 0 (x / (d * d)), mertensR (x / k / (d * d)) = 1 := by
    intro d hd
    obtain ⟨hd0, hdx⟩ := mem_Ioc.mp hd
    have h1 : d * d ≤ x := Nat.le_sqrt.mp hdx
    have hpos : 1 ≤ x / (d * d) := (Nat.one_le_div_iff (Nat.mul_pos hd0 hd0)).mpr h1
    rw [← floorSum_mertensR hpos, floorSum]
    refine sum_congr rfl fun k _ => ?_
    rw [Nat.div_div_eq_div_mul, mul_comm k, ← Nat.div_div_eq_div_mul]
  rw [sum_congr rfl hinner]
  simp

/-- **`L` in terms of `M`.** `L(x) = Σ_{d≤√x} M(⌊x/d²⌋)`. -/
theorem liouvilleR_eq_squareMertens (x : ℕ) : liouvilleR x = squareMertens x := by
  refine eq_of_floorSum_eq (by simp [liouvilleR]) (by simp [squareMertens]) (fun y => ?_) x
  rw [floorSum_liouvilleR, floorSum_squareMertens]

private lemma sum_inv_mul_self_le (J : ℕ) : ∑ d ∈ Ioc 0 J, 1 / ((d : ℝ) * d) ≤ 2 := by
  have h : ∀ J : ℕ, 1 ≤ J → ∑ d ∈ Ioc 0 J, 1 / ((d : ℝ) * d) ≤ 2 - 1 / (J : ℝ) := by
    intro J hJ
    induction J, hJ using Nat.le_induction with
    | base => norm_num
    | succ J hJ ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le J)]
      have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
      have hkey : 1 / (((J + 1 : ℕ) : ℝ) * ((J + 1 : ℕ) : ℝ)) ≤ 1 / (J : ℝ) - 1 / ((J + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ hJR.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp
  · have := h J hJ
    have h2 : (0 : ℝ) ≤ 1 / (J : ℝ) := by positivity
    linarith

/-- **The Mertens level bounds the Liouville sum.** -/
theorem abs_liouvilleR_le {η : ℝ} (hη : 0 ≤ η) (hM : ∀ y : ℕ, |mertensR y| ≤ η * y) (x : ℕ) :
    |liouvilleR x| ≤ 2 * η * x := by
  rw [liouvilleR_eq_squareMertens, squareMertens]
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hterm : ∀ d ∈ Ioc 0 (Nat.sqrt x), |mertensR (x / (d * d))| ≤ η * x * (1 / ((d : ℝ) * d)) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
    refine (hM _).trans ?_
    have hdiv : ((x / (d * d) : ℕ) : ℝ) ≤ (x : ℝ) / ((d : ℝ) * d) := by
      have := Nat.cast_div_le (α := ℝ) (m := x) (n := d * d)
      push_cast at this
      exact this
    calc η * ((x / (d * d) : ℕ) : ℝ) ≤ η * ((x : ℝ) / ((d : ℝ) * d)) :=
          mul_le_mul_of_nonneg_left hdiv hη
      _ = _ := by ring
  calc _ ≤ ∑ d ∈ Ioc 0 (Nat.sqrt x), |mertensR (x / (d * d))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 (Nat.sqrt x), η * x * (1 / ((d : ℝ) * d)) := sum_le_sum hterm
    _ = η * x * ∑ d ∈ Ioc 0 (Nat.sqrt x), 1 / ((d : ℝ) * d) := by rw [mul_sum]
    _ ≤ η * x * 2 := mul_le_mul_of_nonneg_left (sum_inv_mul_self_le _) (by positivity)
    _ = _ := by ring

/-- The parity ledger: the term of `two_mul_coeff_one_mul_card_le` that pays the factor `2`. -/
def parityLedger (c : ℕ →₀ ℤ) (x : ℕ) : ℝ :=
  ∑ k ∈ c.support, (c k : ℝ) * ((ArithmeticFunction.liouville k : ℝ) * liouvilleR (x / k))

/-- **The parity ledger is bounded by the Mertens level.** -/
theorem abs_parityLedger_le {η : ℝ} (hη : 0 ≤ η) (hM : ∀ y : ℕ, |mertensR y| ≤ η * y)
    {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (x : ℕ) :
    |parityLedger c x| ≤ 2 * η * (∑ k ∈ c.support, |(c k : ℝ)| / k) * x := by
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  rw [parityLedger, mul_assoc, sum_mul, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h
    exact Finsupp.mem_support_iff.mp hk hc0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hlam : |(ArithmeticFunction.liouville k : ℝ)| = 1 := by
    rw [ArithmeticFunction.liouville_apply hk0.ne']
    push_cast
    simp [abs_pow]
  rw [abs_mul, abs_mul, hlam, one_mul]
  have hL := abs_liouvilleR_le hη hM (x / k)
  have hdiv : ((x / k : ℕ) : ℝ) ≤ (x : ℝ) / k := Nat.cast_div_le
  have h3 : |liouvilleR (x / k)| ≤ 2 * η * ((x : ℝ) / k) :=
    hL.trans (mul_le_mul_of_nonneg_left hdiv (by positivity))
  calc |(c k : ℝ)| * |liouvilleR (x / k)| ≤ |(c k : ℝ)| * (2 * η * ((x : ℝ) / k)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = _ := by ring

end GaloisForLFunctions.RigidArithmeticOfCuts
