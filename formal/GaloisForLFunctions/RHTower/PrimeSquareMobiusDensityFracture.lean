import GaloisForLFunctions.RHTower.PrimeSquareMobiusSectorFracture
import GaloisForLFunctions.RHTower.Sieve.MoebiusMaximalWindow
import GaloisForLFunctions.RHTower.Sieve.SquarefreeWindowCount

/-!
# The density-side sector fracture of the finite Möbius clocks

This file formalizes §6, equations (33)--(37), of the card
`prime-square-mobius-fourier-complementary-record-law`.
-/

open Finset ArithmeticFunction Filter Topology

namespace RHTower

noncomputable section

/-! ## Elementary transfer lemmas for the local clock -/

theorem localMobiusNat_mul_left {q d c : ℕ} (hq : Nat.Prime q) (hqd : ¬ q ∣ d) :
    localMobiusNat q (d * c) = localMobiusNat q c := by
  have h1 : q ∣ d * c ↔ q ∣ c := by
    constructor
    · intro h
      rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
      · exact absurd h' hqd
      · exact h'
    · exact fun h => Dvd.dvd.mul_left h d
  have h2 : q ^ 2 ∣ d * c ↔ q ^ 2 ∣ c := by
    constructor
    · intro h
      have hcop : Nat.Coprime (q ^ 2) d := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqd |>.pow_left 2
      exact (Nat.Coprime.dvd_of_dvd_mul_left hcop h)
    · exact fun h => Dvd.dvd.mul_left h d
  simp only [localMobiusNat, h1, h2]

theorem eulerClockNat_mul_left {P : Finset ℕ} {d c : ℕ} (hP : ∀ q ∈ P, Nat.Prime q)
    (hd : ∀ q ∈ P, ¬ q ∣ d) : eulerClockNat P (d * c) = eulerClockNat P c := by
  refine Finset.prod_congr rfl fun q hq => ?_
  exact localMobiusNat_mul_left (hP q hq) (hd q hq)

theorem abs_localMobiusNat_le_one (p n : ℕ) : |localMobiusNat p n| ≤ 1 := by
  rw [localMobiusNat]
  by_cases h1 : p ^ 2 ∣ n
  · simp [h1]
  · by_cases h2 : p ∣ n <;> simp [h1, h2]

theorem abs_eulerClockNat_le_one (P : Finset ℕ) (n : ℕ) : |eulerClockNat P n| ≤ 1 := by
  rw [eulerClockNat, Finset.abs_prod]
  calc ∏ p ∈ P, |localMobiusNat p n| ≤ ∏ _p ∈ P, (1 : ℤ) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => abs_localMobiusNat_le_one i n)
    _ = 1 := by simp

/-- Reindexing a sum over the multiples of `d` in `[1, X]`. -/
theorem sum_Icc_dvd_reindex {M : Type*} [AddCommMonoid M] (d X : ℕ) (hd : 0 < d) (f : ℕ → M) :
    ∑ n ∈ (Finset.Icc 1 X).filter (fun n => d ∣ n), f n
      = ∑ c ∈ Finset.Icc 1 (X / d), f (d * c) := by
  classical
  refine (Finset.sum_nbij' (i := fun c => d * c) (j := fun n => n / d) ?_ ?_ ?_ ?_ ?_).symm
  · intro c hc
    rw [Finset.mem_Icc] at hc
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨c, rfl⟩⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hd).mp hc.2
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hn2⟩, hdvd⟩ := hn
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hn2⟩
    exact Nat.one_le_div_iff hd |>.mpr (Nat.le_of_dvd (by omega) hdvd)
  · intro c hc
    exact Nat.mul_div_cancel_left c hd
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro c _
    rfl

/-! ## The mean of the squared clock -/

/-- The summatory function of `m_P²`. -/
def clockSqSum (P : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, ((eulerClockNat P n : ℤ) : ℝ) ^ 2

theorem localMobiusNat_sq (p n : ℕ) :
    (localMobiusNat p n) ^ 2 = if p ^ 2 ∣ n then 0 else 1 := by
  rw [localMobiusNat]
  by_cases h1 : p ^ 2 ∣ n
  · simp [h1]
  · by_cases h2 : p ∣ n <;> simp [h1, h2]

theorem clockSqSum_insert {P : Finset ℕ} {p : ℕ} (hp : Nat.Prime p) (hpP : p ∉ P)
    (hP : ∀ q ∈ P, Nat.Prime q) (X : ℕ) :
    clockSqSum (insert p P) X = clockSqSum P X - clockSqSum P (X / p ^ 2) := by
  classical
  have hpsq : 0 < p ^ 2 := pow_pos hp.pos 2
  have hsplit : ∀ n : ℕ, ((eulerClockNat (insert p P) n : ℤ) : ℝ) ^ 2
      = ((eulerClockNat P n : ℤ) : ℝ) ^ 2
        - (if p ^ 2 ∣ n then ((eulerClockNat P n : ℤ) : ℝ) ^ 2 else 0) := by
    intro n
    rw [eulerClockNat, Finset.prod_insert hpP, ← eulerClockNat]
    push_cast
    rw [mul_pow, ← Int.cast_pow, localMobiusNat_sq]
    by_cases h : p ^ 2 ∣ n <;> simp [h]
  rw [clockSqSum, Finset.sum_congr rfl (fun n _ => hsplit n), Finset.sum_sub_distrib,
    ← Finset.sum_filter, sum_Icc_dvd_reindex (p ^ 2) X hpsq]
  congr 1
  rw [clockSqSum]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  refine eulerClockNat_mul_left hP fun q hq => ?_
  intro hcon
  have hqp : q ∣ p := (hP q hq).dvd_of_dvd_pow hcon
  have : q = p := ((Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hqp)
  exact hpP (this ▸ hq)


/-! ## Elementary limits of natural division -/

theorem tendsto_natDiv_div_self {d : ℕ} (hd : 0 < d) :
    Tendsto (fun X : ℕ => ((X / d : ℕ) : ℝ) / (X : ℝ)) atTop (𝓝 ((d : ℝ)⁻¹)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmain : ∀ X : ℕ, 0 < X →
      ((X / d : ℕ) : ℝ) / (X : ℝ) = (d : ℝ)⁻¹ - ((X % d : ℕ) : ℝ) / ((d : ℝ) * (X : ℝ)) := by
    intro X hX
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hkey : (d : ℝ) * ((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) = (X : ℝ) := by
      exact_mod_cast Nat.div_add_mod X d
    field_simp
    linarith [hkey]
  have herr : Tendsto (fun X : ℕ => ((X % d : ℕ) : ℝ) / ((d : ℝ) * (X : ℝ))) atTop (𝓝 0) := by
    have hbound : ∀ X : ℕ, 0 < X →
        |((X % d : ℕ) : ℝ) / ((d : ℝ) * (X : ℝ))| ≤ 1 / (X : ℝ) := by
      intro X hX
      have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
      have hmod : ((X % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt X hd
      have hmod0 : (0 : ℝ) ≤ ((X % d : ℕ) : ℝ) := by positivity
      rw [abs_of_nonneg (by positivity)]
      calc ((X % d : ℕ) : ℝ) / ((d : ℝ) * (X : ℝ)) ≤ (d : ℝ) / ((d : ℝ) * (X : ℝ)) := by
            gcongr
        _ = 1 / (X : ℝ) := by field_simp
    have hlim : Tendsto (fun X : ℕ => 1 / (X : ℝ)) atTop (𝓝 0) := by
      have h := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa [Function.comp_def, one_div] using h
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    rw [NormedAddGroup.tendsto_nhds_zero] at hlim
    filter_upwards [hlim ε hε, Filter.eventually_gt_atTop 0] with X hX1 hX2
    calc ‖((X % d : ℕ) : ℝ) / ((d : ℝ) * (X : ℝ))‖ ≤ 1 / (X : ℝ) := by
          rw [Real.norm_eq_abs]; exact hbound X hX2
      _ ≤ ‖(1 : ℝ) / (X : ℝ)‖ := le_abs_self _
      _ < ε := hX1
  have := (tendsto_const_nhds (x := ((d : ℝ))⁻¹) (f := (atTop : Filter ℕ))).sub herr
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with X hX
  exact (hmain X hX).symm

/-! ## The mean of the squared clock -/

theorem clockSqSum_empty (X : ℕ) : clockSqSum ∅ X = (X : ℝ) := by
  rw [clockSqSum]
  simp [eulerClockNat, Nat.card_Icc]

theorem tendsto_clockSqSum {P : Finset ℕ} (hP : ∀ q ∈ P, Nat.Prime q) :
    Tendsto (fun X : ℕ => clockSqSum P X / (X : ℝ)) atTop
      (𝓝 (∏ p ∈ P, (1 - ((p : ℝ) ^ 2)⁻¹))) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ)))
      filter_upwards [Filter.eventually_gt_atTop 0] with X hX
      have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
      rw [clockSqSum_empty]
      field_simp
  | insert p P hpP ih =>
      have hP' : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
      have hp : Nat.Prime p := hP p (Finset.mem_insert_self p P)
      have hpsq : 0 < p ^ 2 := pow_pos hp.pos 2
      have hih := ih hP'
      have hsecond : Tendsto (fun X : ℕ => clockSqSum P (X / p ^ 2) / (X : ℝ)) atTop
          (𝓝 ((∏ q ∈ P, (1 - ((q : ℝ) ^ 2)⁻¹)) * (((p : ℝ) ^ 2)⁻¹))) := by
        have hdiv : Tendsto (fun X : ℕ => X / p ^ 2) atTop atTop :=
          Filter.tendsto_atTop_atTop.mpr fun b => ⟨b * p ^ 2, fun a ha =>
            (Nat.le_div_iff_mul_le hpsq).mpr ha⟩
        have h1 := hih.comp hdiv
        have h2 := tendsto_natDiv_div_self hpsq
        have hcast : ((p ^ 2 : ℕ) : ℝ)⁻¹ = ((p : ℝ) ^ 2)⁻¹ := by push_cast; ring
        rw [hcast] at h2
        have hmul := h1.mul h2
        refine hmul.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop 0] with X hX
        simp only [Function.comp_apply]
        by_cases hz : X / p ^ 2 = 0
        · have hzero : clockSqSum P (X / p ^ 2) = 0 := by
            rw [clockSqSum, hz]
            simp
          rw [hzero, hz]
          simp
        · have hzR : ((X / p ^ 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz
          field_simp
      have hcomb := hih.sub hsecond
      have hlimit : Tendsto (fun X : ℕ => clockSqSum (insert p P) X / (X : ℝ)) atTop
          (𝓝 ((∏ q ∈ P, (1 - ((q : ℝ) ^ 2)⁻¹))
            - (∏ q ∈ P, (1 - ((q : ℝ) ^ 2)⁻¹)) * (((p : ℝ) ^ 2)⁻¹))) := by
        refine hcomb.congr' ?_
        filter_upwards with X
        rw [clockSqSum_insert hp hpP hP' X, sub_div]
      have hval : (∏ q ∈ P, (1 - ((q : ℝ) ^ 2)⁻¹))
            - (∏ q ∈ P, (1 - ((q : ℝ) ^ 2)⁻¹)) * (((p : ℝ) ^ 2)⁻¹)
          = ∏ q ∈ insert p P, (1 - ((q : ℝ) ^ 2)⁻¹) := by
        rw [Finset.prod_insert hpP]
        ring
      rw [← hval]
      exact hlimit


/-! ## The cross term `∑ μ(n) m_P(n)` -/

/-- The summatory function of `μ · m_P`, equation (33). -/
def mobiusClockSum (P : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) * ((eulerClockNat P n : ℤ) : ℝ)

/-- The part of that sum supported on the multiples of `p`. -/
def mobiusClockDvdSum (P : Finset ℕ) (p X : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 X).filter (fun n => p ∣ n),
    ((moebius n : ℤ) : ℝ) * ((eulerClockNat P n : ℤ) : ℝ)

theorem abs_moebius_mul_clock_le (P : Finset ℕ) (n : ℕ) :
    |((moebius n : ℤ) : ℝ) * ((eulerClockNat P n : ℤ) : ℝ)| ≤ 1 := by
  rw [abs_mul]
  have h1 : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
    rcases moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num
  have h2 : |((eulerClockNat P n : ℤ) : ℝ)| ≤ 1 := by
    have := abs_eulerClockNat_le_one P n
    have hcast : |((eulerClockNat P n : ℤ) : ℝ)| = ((|eulerClockNat P n| : ℤ) : ℝ) := by
      push_cast
      rw [abs_eq_abs]
      left
      rfl
    rw [hcast]
    exact_mod_cast this
  nlinarith [abs_nonneg (((moebius n : ℤ) : ℝ)), abs_nonneg (((eulerClockNat P n : ℤ) : ℝ))]

theorem abs_mobiusClockSum_le (P : Finset ℕ) (X : ℕ) : |mobiusClockSum P X| ≤ (X : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => abs_moebius_mul_clock_le P n) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  simp

theorem abs_mobiusClockDvdSum_le (P : Finset ℕ) (p X : ℕ) :
    |mobiusClockDvdSum P p X| ≤ (X : ℝ) := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => abs_moebius_mul_clock_le P n) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : ((Finset.Icc 1 X).filter (fun n => p ∣ n)).card ≤ X := by
    have := Finset.card_filter_le (Finset.Icc 1 X) (fun n => p ∣ n)
    rw [Nat.card_Icc] at this
    omega
  exact_mod_cast hcard

theorem moebius_mul_localMobiusNat {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    ((moebius n : ℤ) : ℝ) * ((localMobiusNat p n : ℤ) : ℝ)
      = ((moebius n : ℤ) : ℝ) - 2 * (if p ∣ n then ((moebius n : ℤ) : ℝ) else 0) := by
  by_cases h2 : p ^ 2 ∣ n
  · have hzero : moebius n = 0 := by
      refine moebius_eq_zero_of_not_squarefree ?_
      intro hsq
      exact hp.not_isUnit (hsq p (by rw [← pow_two]; exact h2))
    have hpn : p ∣ n := dvd_trans (dvd_pow_self p two_ne_zero) h2
    simp [localMobiusNat, h2, hpn, hzero]
  · by_cases h1 : p ∣ n
    · simp only [localMobiusNat, if_neg h2, if_pos h1]
      push_cast
      ring
    · simp only [localMobiusNat, if_neg h2, if_neg h1]
      push_cast
      ring

theorem mobiusClockSum_insert {P : Finset ℕ} {p : ℕ} (hp : Nat.Prime p) (hpP : p ∉ P) (X : ℕ) :
    mobiusClockSum (insert p P) X
      = mobiusClockSum P X - 2 * mobiusClockDvdSum P p X := by
  classical
  have hterm : ∀ n : ℕ,
      ((moebius n : ℤ) : ℝ) * ((eulerClockNat (insert p P) n : ℤ) : ℝ)
        = ((moebius n : ℤ) : ℝ) * ((eulerClockNat P n : ℤ) : ℝ)
          - 2 * (if p ∣ n then
              ((moebius n : ℤ) : ℝ) * ((eulerClockNat P n : ℤ) : ℝ) else 0) := by
    intro n
    rw [eulerClockNat, Finset.prod_insert hpP, ← eulerClockNat]
    push_cast
    have h := moebius_mul_localMobiusNat hp n
    by_cases hd : p ∣ n
    · simp only [if_pos hd] at h ⊢
      linear_combination ((eulerClockNat P n : ℤ) : ℝ) * h
    · simp only [if_neg hd] at h ⊢
      linear_combination ((eulerClockNat P n : ℤ) : ℝ) * h
  rw [mobiusClockSum, Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_filter]
  rfl

theorem mobiusClockDvdSum_rec {P : Finset ℕ} {p : ℕ} (hp : Nat.Prime p) (hpP : p ∉ P)
    (hP : ∀ q ∈ P, Nat.Prime q) (X : ℕ) :
    mobiusClockDvdSum P p X
      = - mobiusClockSum P (X / p) + mobiusClockDvdSum P p (X / p) := by
  classical
  have hqp : ∀ q ∈ P, ¬ q ∣ p := by
    intro q hq hdvd
    have : q = p := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hdvd
    exact hpP (this ▸ hq)
  have hstep : ∀ c : ℕ, 1 ≤ c →
      ((moebius (p * c) : ℤ) : ℝ) * ((eulerClockNat P (p * c) : ℤ) : ℝ)
        = -(((moebius c : ℤ) : ℝ) * ((eulerClockNat P c : ℤ) : ℝ))
          + (if p ∣ c then ((moebius c : ℤ) : ℝ) * ((eulerClockNat P c : ℤ) : ℝ) else 0) := by
    intro c hc
    rw [eulerClockNat_mul_left hP hqp]
    by_cases hd : p ∣ c
    · have hnsq : ¬ Squarefree (p * c) := by
        intro hsq
        obtain ⟨e, rfl⟩ := hd
        exact hp.not_isUnit (hsq p ⟨e, by ring⟩)
      rw [moebius_eq_zero_of_not_squarefree hnsq]
      simp [hd]
    · have hcop : Nat.Coprime p c := (Nat.Prime.coprime_iff_not_dvd hp).mpr hd
      rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp, if_neg hd]
      push_cast
      ring
  rw [mobiusClockDvdSum, sum_Icc_dvd_reindex p X hp.pos]
  rw [Finset.sum_congr rfl (fun c hc => hstep c (Finset.mem_Icc.mp hc).1)]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_filter]
  rfl


/-! ## The geometric transfer -/

theorem geom_half_sum (k : ℕ) :
    ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (j + 1) = 1 - (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring

theorem tendsto_mobiusClockDvdSum {P : Finset ℕ} {p : ℕ} (hp : Nat.Prime p) (hpP : p ∉ P)
    (hP : ∀ q ∈ P, Nat.Prime q)
    (hA : Tendsto (fun X : ℕ => mobiusClockSum P X / (X : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ => mobiusClockDvdSum P p X / (X : ℝ)) atTop (𝓝 0) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hpowle : ∀ m : ℕ, ((2 : ℝ)) ^ m ≤ ((p : ℕ) : ℝ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, pow_succ]
        have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ m := by positivity
        nlinarith [ih, h2]
  have hdivbound : ∀ X m : ℕ, ((X / p ^ m : ℕ) : ℝ) ≤ (X : ℝ) * (1 / 2 : ℝ) ^ m := by
    intro X m
    have hnat : (X / p ^ m) * p ^ m ≤ X := Nat.div_mul_le_self X (p ^ m)
    have hnatR : ((X / p ^ m : ℕ) : ℝ) * ((p : ℝ) ^ m) ≤ (X : ℝ) := by exact_mod_cast hnat
    have hq : ((X / p ^ m : ℕ) : ℝ) * ((2 : ℝ) ^ m) ≤ (X : ℝ) := by
      have hnn : (0 : ℝ) ≤ ((X / p ^ m : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hnatR, hpowle m, hnn]
    have hstep1 : ((X / p ^ m : ℕ) : ℝ) * ((2 : ℝ) ^ m) * (1 / 2 : ℝ) ^ m
        ≤ (X : ℝ) * (1 / 2 : ℝ) ^ m := mul_le_mul_of_nonneg_right hq (by positivity)
    have hsimp : ((X / p ^ m : ℕ) : ℝ) * ((2 : ℝ) ^ m) * (1 / 2 : ℝ) ^ m
        = ((X / p ^ m : ℕ) : ℝ) := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    linarith [hstep1, hsimp.le, hsimp.ge]
  have hiter : ∀ k X : ℕ, |mobiusClockDvdSum P p X|
      ≤ (∑ j ∈ Finset.range k, |mobiusClockSum P (X / p ^ (j + 1))|)
        + |mobiusClockDvdSum P p (X / p ^ k)| := by
    intro k
    induction k with
    | zero => intro X; simp
    | succ k ih =>
        intro X
        refine le_trans (ih X) ?_
        have hrec := mobiusClockDvdSum_rec hp hpP hP (X / p ^ k)
        have hb : |mobiusClockDvdSum P p (X / p ^ k)|
            ≤ |mobiusClockSum P (X / p ^ k / p)|
              + |mobiusClockDvdSum P p (X / p ^ k / p)| := by
          rw [hrec]
          have h := norm_add_le (-(mobiusClockSum P (X / p ^ k / p)))
            (mobiusClockDvdSum P p (X / p ^ k / p))
          rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg] at h
          exact h
        have hdd : X / p ^ k / p = X / p ^ (k + 1) := by
          rw [Nat.div_div_eq_div_mul, pow_succ]
        rw [hdd] at hb
        rw [Finset.sum_range_succ]
        linarith [hb]
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set ε' : ℝ := ε / 4 with hε'def
  have hε' : 0 < ε' := by positivity
  rw [NormedAddGroup.tendsto_nhds_zero] at hA
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hA ε' hε')
  set N : ℕ := max N₀ 1 with hNdef
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N₀ 1)
  have hAll : ∀ X : ℕ, |mobiusClockSum P X| ≤ ε' * (X : ℝ) + (N : ℝ) := by
    intro X
    by_cases hX : N ≤ X
    · have hX0 : 0 < X := lt_of_lt_of_le hNpos hX
      have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX0
      have h1 : ‖mobiusClockSum P X / (X : ℝ)‖ < ε' :=
        hN₀ X (le_trans (le_max_left N₀ 1) hX)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hXR, div_lt_iff₀ hXR] at h1
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      linarith
    · have hXN : (X : ℝ) ≤ (N : ℝ) := by
        have hle : X ≤ N := by omega
        exact_mod_cast hle
      have h1 := abs_mobiusClockSum_le P X
      have h2 : (0 : ℝ) ≤ ε' * (X : ℝ) := by positivity
      linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε' (by norm_num : (1 / 2 : ℝ) < 1)
  have hmain : ∀ X : ℕ, 0 < X →
      |mobiusClockDvdSum P p X| ≤ 2 * ε' * (X : ℝ) + (k : ℝ) * (N : ℝ) := by
    intro X hX
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hbound1 : ∀ j : ℕ, |mobiusClockSum P (X / p ^ (j + 1))|
        ≤ ε' * ((X : ℝ) * (1 / 2 : ℝ) ^ (j + 1)) + (N : ℝ) := by
      intro j
      refine le_trans (hAll _) ?_
      have := mul_le_mul_of_nonneg_left (hdivbound X (j + 1)) hε'.le
      linarith
    have hsum : (∑ j ∈ Finset.range k, |mobiusClockSum P (X / p ^ (j + 1))|)
        ≤ ε' * (X : ℝ) + (k : ℝ) * (N : ℝ) := by
      have h1 : (∑ j ∈ Finset.range k, |mobiusClockSum P (X / p ^ (j + 1))|)
          ≤ ∑ j ∈ Finset.range k, (ε' * ((X : ℝ) * (1 / 2 : ℝ) ^ (j + 1)) + (N : ℝ)) :=
        Finset.sum_le_sum fun j _ => hbound1 j
      have h2 : ∑ j ∈ Finset.range k, (ε' * ((X : ℝ) * (1 / 2 : ℝ) ^ (j + 1)) + (N : ℝ))
          = (ε' * (X : ℝ)) * (1 - (1 / 2 : ℝ) ^ k) + (k : ℝ) * (N : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        congr 1
        have hcongr : ∀ j : ℕ, ε' * ((X : ℝ) * (1 / 2 : ℝ) ^ (j + 1))
            = (ε' * (X : ℝ)) * (1 / 2 : ℝ) ^ (j + 1) := fun j => by ring
        rw [Finset.sum_congr rfl (fun j _ => hcongr j), ← Finset.mul_sum, geom_half_sum]
      rw [h2] at h1
      have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
      have hprod : (0 : ℝ) ≤ ε' * (X : ℝ) := by positivity
      nlinarith [h1, hnn, hprod]
    have htail : |mobiusClockDvdSum P p (X / p ^ k)| ≤ ε' * (X : ℝ) := by
      have h1 := abs_mobiusClockDvdSum_le P p (X / p ^ k)
      have h2 := hdivbound X k
      have h3 : (X : ℝ) * (1 / 2 : ℝ) ^ k ≤ (X : ℝ) * ε' :=
        mul_le_mul_of_nonneg_left hk.le hXR.le
      nlinarith [h1, h2, h3]
    linarith [hiter k X, hsum, htail]
  have hthr : ∃ M : ℕ, ∀ X : ℕ, M ≤ X → (k : ℝ) * (N : ℝ) < ε' * (X : ℝ) := by
    obtain ⟨M, hM⟩ := exists_nat_gt (((k : ℝ) * (N : ℝ) + 1) / ε')
    refine ⟨M, fun X hX => ?_⟩
    have hXR : ((M : ℝ)) ≤ (X : ℝ) := by exact_mod_cast hX
    have h1 : ((k : ℝ) * (N : ℝ) + 1) / ε' < (X : ℝ) := lt_of_lt_of_le hM hXR
    rw [div_lt_iff₀ hε'] at h1
    linarith
  obtain ⟨M, hM⟩ := hthr
  filter_upwards [Filter.eventually_ge_atTop (max M 1)] with X hX
  have hX1 : 0 < X := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right M 1) hX)
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX1
  have h1 := hmain X hX1
  have h2 := hM X (le_trans (le_max_left M 1) hX)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hXR, div_lt_iff₀ hXR]
  have hεX : (0 : ℝ) < ε * (X : ℝ) := by positivity
  have hkey : 2 * ε' * (X : ℝ) + (k : ℝ) * (N : ℝ) < ε * (X : ℝ) := by
    rw [hε'def] at h2 ⊢
    linarith
  linarith


/-- **Equation (33).**  Every finite Euler clock is asymptotically orthogonal to `μ` in natural
density. -/
theorem tendsto_mobiusClockSum {P : Finset ℕ} (hP : ∀ q ∈ P, Nat.Prime q) :
    Tendsto (fun X : ℕ => mobiusClockSum P X / (X : ℝ)) atTop (𝓝 0) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      have heq : ∀ X : ℕ, mobiusClockSum ∅ X = Sieve.mertensM X := by
        intro X
        rw [mobiusClockSum, Sieve.mertensM]
        rw [show Finset.range (X + 1) = Finset.Icc 0 X by
          ext n; simp]
        rw [show Finset.Icc 0 X = insert 0 (Finset.Icc 1 X) by
          ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
        rw [Finset.sum_insert (by simp)]
        simp [eulerClockNat]
      have hM := Sieve.tendsto_abs_mertensM_div
      rw [NormedAddGroup.tendsto_nhds_zero] at hM ⊢
      intro ε hε
      filter_upwards [hM ε hε, Filter.eventually_gt_atTop 0] with X h1 h2
      have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast h2
      rw [heq X, Real.norm_eq_abs, abs_div, abs_of_pos hXR]
      calc |Sieve.mertensM X| / (X : ℝ) ≤ ‖|Sieve.mertensM X| / (X : ℝ)‖ := le_abs_self _
        _ < ε := h1
  | insert p P hpP ih =>
      have hP' : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
      have hp : Nat.Prime p := hP p (Finset.mem_insert_self p P)
      have hA := ih hP'
      have hB := tendsto_mobiusClockDvdSum hp hpP hP' hA
      have hcomb : Tendsto (fun X : ℕ => mobiusClockSum P X / (X : ℝ)
          - 2 * (mobiusClockDvdSum P p X / (X : ℝ))) atTop (𝓝 0) := by
        have h := hA.sub (hB.const_mul (2 : ℝ))
        simpa using h
      refine hcomb.congr fun X => ?_
      rw [mobiusClockSum_insert hp hpP X, sub_div, mul_div_assoc]

/-! ## The squarefree density -/

theorem tendsto_natSqrt_atTop : Tendsto (fun X : ℕ => Nat.sqrt X) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b * b, fun a ha => ?_⟩
  exact Nat.le_sqrt.mpr ha

/-- **Equation (34).**  The squarefree density is `1/ζ(2)`. -/
theorem tendsto_squarefree_density :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2) / (X : ℝ))
      atTop (𝓝 Sieve.squarefreeDensity) := by
  have hkey : ∀ X : ℕ, 0 < X →
      |(∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2) / (X : ℝ) - Sieve.squarefreeDensity|
        ≤ ((Nat.sqrt X : ℕ) + 1 : ℝ) / (X : ℝ) + 1 / ((Nat.sqrt X : ℕ) + 1 : ℝ) := by
    intro X hX
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hR : 1 ≤ Nat.sqrt X + 1 := by omega
    have hRM : 0 + X ≤ (Nat.sqrt X + 1) ^ 2 := by
      have h := Nat.lt_succ_sqrt' X
      rw [Nat.succ_eq_add_one] at h
      have hsq : (Nat.sqrt X + 1) ^ 2 = (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := by ring
      omega
    have hIoc : Finset.Ioc 0 X = Finset.Icc 1 X := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    have hbase := Sieve.abs_window_squarefree_sub_le (t := 0) (L := X)
      (R := Nat.sqrt X + 1) hR hRM
    rw [zero_add, hIoc] at hbase
    have hRpos : (0 : ℝ) < ((Nat.sqrt X + 1 : ℕ) : ℝ) := by positivity
    have hdiv : |(∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2) / (X : ℝ)
        - Sieve.squarefreeDensity|
        = |(∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2)
            - (X : ℝ) * Sieve.squarefreeDensity| / (X : ℝ) := by
      have hEq : (∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2) / (X : ℝ)
          - Sieve.squarefreeDensity
          = ((∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2)
              - (X : ℝ) * Sieve.squarefreeDensity) / (X : ℝ) := by
        field_simp
      rw [hEq, abs_div, abs_of_pos hXR]
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXR
    have hRne : ((Nat.sqrt X : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    rw [hdiv, div_le_iff₀ hXR]
    refine le_trans hbase (le_of_eq ?_)
    push_cast
    field_simp
  have hbound : Tendsto (fun X : ℕ =>
      ((Nat.sqrt X : ℕ) + 1 : ℝ) / (X : ℝ) + 1 / ((Nat.sqrt X : ℕ) + 1 : ℝ)) atTop (𝓝 0) := by
    have hA : Tendsto (fun X : ℕ => ((Nat.sqrt X : ℕ) + 1 : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
      have hle : ∀ X : ℕ, 0 < X →
          |((Nat.sqrt X : ℕ) + 1 : ℝ) / (X : ℝ)| ≤ (Real.sqrt X + 1) / (X : ℝ) := by
        intro X hX
        have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
        rw [abs_of_nonneg (by positivity)]
        gcongr
        exact Sieve.natSqrt_le_sqrt X
      have hlim : Tendsto (fun X : ℕ => (Real.sqrt X + 1) / (X : ℝ)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun X : ℝ => (Real.sqrt X + 1) / X) atTop (𝓝 0) := by
          have ha : Tendsto (fun X : ℝ => Real.sqrt X / X) atTop (𝓝 0) := by
            have hcongr : ∀ᶠ X : ℝ in atTop, (Real.sqrt X)⁻¹ = Real.sqrt X / X := by
              filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
              rw [eq_div_iff hX.ne', inv_mul_eq_div, div_eq_iff (Real.sqrt_ne_zero'.mpr hX)]
              exact (Real.mul_self_sqrt hX.le).symm
            refine Tendsto.congr' hcongr ?_
            exact Real.tendsto_sqrt_atTop.inv_tendsto_atTop
          have hb : Tendsto (fun X : ℝ => (1 : ℝ) / X) atTop (𝓝 0) := by
            simpa [one_div] using tendsto_inv_atTop_zero
          have hsum := ha.add hb
          rw [add_zero] at hsum
          refine hsum.congr fun X => ?_
          rw [add_div]
        exact h1.comp tendsto_natCast_atTop_atTop
      rw [NormedAddGroup.tendsto_nhds_zero]
      intro ε hε
      rw [NormedAddGroup.tendsto_nhds_zero] at hlim
      filter_upwards [hlim ε hε, Filter.eventually_gt_atTop 0] with X h1 h2
      calc ‖((Nat.sqrt X : ℕ) + 1 : ℝ) / (X : ℝ)‖
          = |((Nat.sqrt X : ℕ) + 1 : ℝ) / (X : ℝ)| := Real.norm_eq_abs _
        _ ≤ (Real.sqrt X + 1) / (X : ℝ) := hle X h2
        _ ≤ ‖(Real.sqrt X + 1) / (X : ℝ)‖ := le_abs_self _
        _ < ε := h1
    have hB : Tendsto (fun X : ℕ => 1 / ((Nat.sqrt X : ℕ) + 1 : ℝ)) atTop (𝓝 0) := by
      have hdiv : Tendsto (fun X : ℕ => ((Nat.sqrt X : ℕ) : ℝ) + 1) atTop atTop := by
        have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_natSqrt_atTop
        have h2 : Tendsto (fun X : ℕ => ((Nat.sqrt X : ℕ) : ℝ)) atTop atTop := by
          simpa [Function.comp_def] using h
        simpa using h2.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
      exact hdiv.inv_tendsto_atTop.congr fun X => by simp [one_div]
    have hsum := hA.add hB
    rw [add_zero] at hsum
    exact hsum
  have hzero : Tendsto (fun X : ℕ =>
      (∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2) / (X : ℝ) - Sieve.squarefreeDensity)
      atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    rw [NormedAddGroup.tendsto_nhds_zero] at hbound
    filter_upwards [hbound ε hε, Filter.eventually_gt_atTop 0] with X h1 h2
    calc ‖(∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2) / (X : ℝ)
            - Sieve.squarefreeDensity‖
        = |(∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2) / (X : ℝ)
            - Sieve.squarefreeDensity| := Real.norm_eq_abs _
      _ ≤ ((Nat.sqrt X : ℕ) + 1 : ℝ) / (X : ℝ) + 1 / ((Nat.sqrt X : ℕ) + 1 : ℝ) := hkey X h2
      _ ≤ ‖((Nat.sqrt X : ℕ) + 1 : ℝ) / (X : ℝ) + 1 / ((Nat.sqrt X : ℕ) + 1 : ℝ)‖ :=
          le_abs_self _
      _ < ε := h1
  have hfin := hzero.add (tendsto_const_nhds (x := Sieve.squarefreeDensity)
    (f := (atTop : Filter ℕ)))
  rw [zero_add] at hfin
  refine hfin.congr fun X => ?_
  ring

/-! ## The density-side sector fracture -/

/-- **Equations (36)--(37).**  The mean square distance in density between `μ` and the finite
Euler clock of `P` is `1/ζ(2) + ∏_{p ∈ P}(1 − p^(−2))`: the finite clocks converge to `μ`
pointwise while becoming asymptotically orthogonal to it in density. -/
theorem tendsto_density_sector_fracture {P : Finset ℕ} (hP : ∀ q ∈ P, Nat.Prime q) :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.Icc 1 X,
        (((moebius n : ℤ) : ℝ) - ((eulerClockNat P n : ℤ) : ℝ)) ^ 2) / (X : ℝ))
      atTop (𝓝 (Sieve.squarefreeDensity + ∏ p ∈ P, (1 - ((p : ℝ) ^ 2)⁻¹))) := by
  have hexpand : ∀ X : ℕ, (∑ n ∈ Finset.Icc 1 X,
      (((moebius n : ℤ) : ℝ) - ((eulerClockNat P n : ℤ) : ℝ)) ^ 2)
      = (∑ n ∈ Finset.Icc 1 X, ((moebius n : ℤ) : ℝ) ^ 2)
        - 2 * mobiusClockSum P X + clockSqSum P X := by
    intro X
    rw [mobiusClockSum, clockSqSum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hA := tendsto_squarefree_density
  have hB := tendsto_mobiusClockSum hP
  have hC := tendsto_clockSqSum hP
  have hcomb := (hA.sub (hB.const_mul (2 : ℝ))).add hC
  rw [mul_zero, sub_zero] at hcomb
  refine hcomb.congr fun X => ?_
  rw [hexpand X]
  by_cases hX : X = 0
  · subst hX
    simp [mobiusClockSum, clockSqSum]
  · have hXR : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hX
    field_simp

/-- The same statement with the explicit constant `1/ζ(2) = 6/π²`. -/
theorem tendsto_density_sector_fracture_pi {P : Finset ℕ} (hP : ∀ q ∈ P, Nat.Prime q) :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.Icc 1 X,
        (((moebius n : ℤ) : ℝ) - ((eulerClockNat P n : ℤ) : ℝ)) ^ 2) / (X : ℝ))
      atTop (𝓝 (6 / Real.pi ^ 2 + ∏ p ∈ P, (1 - ((p : ℝ) ^ 2)⁻¹))) := by
  have h := tendsto_density_sector_fracture hP
  rwa [Sieve.squarefreeDensity_eq] at h

end

end RHTower
