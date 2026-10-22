import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittMultiplication
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Logarithmic ghost map for the literal big-Witt carrier

The ghost series is `-T f'(T)/f(T)`.  Division here is only by the power-series unit `f`, never by
an integer.  Thus additivity is valid over arbitrary rings.  Injectivity is used only over the
universal torsion-free source ring before descent to arbitrary targets.
-/

namespace RHTower

noncomputable section

open PowerSeries

variable {A : Type*} [CommRing A]

/-- Logarithmic ghost series of a constant-one formal power series. -/
def deningerBigWittLogGhost (f : PowerSeries A)
    (_hf : PowerSeries.constantCoeff f = 1) : PowerSeries A :=
  -(PowerSeries.X * PowerSeries.derivative A f * PowerSeries.invOfUnit f 1)

@[simp] theorem deningerBigWittLogGhost_constantCoeff
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    PowerSeries.constantCoeff (deningerBigWittLogGhost f hf) = 0 := by
  simp [deningerBigWittLogGhost]

theorem deningerBigWittLogGhost_congr
    {f g : PowerSeries A}
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1)
    (h : f = g) :
    deningerBigWittLogGhost f hf = deningerBigWittLogGhost g hg := by
  subst g
  rfl

theorem deningerBigWittLogGhost_mul_self
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    deningerBigWittLogGhost f hf * f =
      -(PowerSeries.X * PowerSeries.derivative A f) := by
  rw [deningerBigWittLogGhost, neg_mul, mul_assoc,
    PowerSeries.invOfUnit_mul f 1 hf]
  simp

/-- The logarithmic ghost transforms ordinary multiplication into addition over every
commutative ring. -/
theorem deningerBigWittLogGhost_mul
    (f g : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    deningerBigWittLogGhost (f * g) (by simp [hf, hg]) =
      deningerBigWittLogGhost f hf + deningerBigWittLogGhost g hg := by
  have hfg : IsUnit (f * g) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hf, hg])
  apply hfg.mul_right_cancel
  rw [deningerBigWittLogGhost_mul_self]
  rw [add_mul]
  rw [← mul_assoc (deningerBigWittLogGhost f hf) f g,
    deningerBigWittLogGhost_mul_self f hf]
  have hgterm : deningerBigWittLogGhost g hg * (f * g) =
      f * (-(PowerSeries.X * PowerSeries.derivative A g)) := by
    calc
      deningerBigWittLogGhost g hg * (f * g) =
          f * (deningerBigWittLogGhost g hg * g) := by ring
      _ = f * (-(PowerSeries.X * PowerSeries.derivative A g)) := by
          rw [deningerBigWittLogGhost_mul_self g hg]
  rw [hgterm]
  change -(PowerSeries.X * PowerSeries.derivativeFun (f * g)) = _
  rw [PowerSeries.derivativeFun_mul]
  simp only [smul_eq_mul]
  change -(PowerSeries.X * (f * PowerSeries.derivative A g +
    g * PowerSeries.derivative A f)) = _
  ring

/-- Geometric inverse of the Euler factor `1-aT^m`, defined coefficientwise without a topology. -/
def deningerBigWittGeom (a : A) (m : ℕ) : PowerSeries A :=
  PowerSeries.mk fun n => if m ∣ n then a ^ (n / m) else 0

@[simp] theorem deningerBigWittGeom_coeff (a : A) (m n : ℕ) :
    PowerSeries.coeff n (deningerBigWittGeom a m) =
      if m ∣ n then a ^ (n / m) else 0 := by
  simp [deningerBigWittGeom]

theorem deningerBigWittGeom_mul_factor (a : A) {m : ℕ} (hm : 0 < m) :
    deningerBigWittGeom a m * deningerBigWittFactor a m = 1 := by
  apply PowerSeries.ext
  intro n
  rw [deningerBigWittFactor, mul_sub, mul_one, map_sub, ← mul_assoc,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C]
  cases n with
  | zero => simp [deningerBigWittGeom, hm.ne']
  | succ n =>
      by_cases hle : m ≤ n + 1
      · rw [if_pos hle]
        by_cases hd : m ∣ n + 1
        · obtain ⟨q, hq⟩ := hd
          have hq0 : q ≠ 0 := by
            intro h
            subst q
            simp at hq
          rw [hq]
          have hsubeq : m * q - m = m * (q - 1) := by
            calc
              m * q - m = m * q - m * 1 := by rw [mul_one]
              _ = m * (q - 1) := (Nat.mul_sub_left_distrib m q 1).symm
          rw [deningerBigWittGeom_coeff, deningerBigWittGeom_coeff, hsubeq,
            Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel_left _ hm]
          have hqeq : q = (q - 1) + 1 := by omega
          rw [hqeq, pow_succ]
          simp [hm.ne']
        · have hsub : ¬m ∣ n + 1 - m := by
            intro hs
            apply hd
            rw [← Nat.sub_add_cancel hle]
            exact dvd_add hs (dvd_refl m)
          simp [deningerBigWittGeom, hd, hsub]
      · rw [if_neg hle]
        have hd : ¬m ∣ n + 1 := by
          intro hd
          exact hle (Nat.le_of_dvd (Nat.succ_pos n) hd)
        simp [deningerBigWittGeom, hd]

theorem deningerBigWittInvFactor_eq_geom (a : A) {m : ℕ} (hm : 0 < m) :
    PowerSeries.invOfUnit (deningerBigWittFactor a m) 1 =
      deningerBigWittGeom a m := by
  have hu : IsUnit (deningerBigWittFactor a m) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr
      (by rw [deningerBigWittFactor_constantCoeff a m hm.ne']; exact isUnit_one)
  apply hu.mul_right_cancel
  rw [PowerSeries.invOfUnit_mul _ 1
      (deningerBigWittFactor_constantCoeff a m hm.ne'),
    deningerBigWittGeom_mul_factor a hm]

theorem deningerBigWittDerivative_factor (a : A) {m : ℕ} (hm : 0 < m) :
    PowerSeries.derivative A (deningerBigWittFactor a m) =
      -(PowerSeries.C ((m : A) * a) * PowerSeries.X ^ (m - 1)) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative]
  simp only [deningerBigWittFactor, map_sub, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul_X_pow, map_neg]
  have heq : n + 1 = m ↔ n = m - 1 := by omega
  simp only [if_neg (Nat.succ_ne_zero n), zero_sub, heq]
  by_cases hnm : n = m - 1 <;> simp [hnm]
  subst n
  have hcast : ((m - 1 : ℕ) : A) + 1 = (m : A) := by
    have hc := congrArg (fun q : ℕ => (q : A)) (Nat.sub_add_cancel hm)
    simpa only [Nat.cast_add, Nat.cast_one] using hc
  rw [hcast]
  change a * (m : A) = (m : A) * a
  ring

theorem deningerBigWittLogGhost_factor (a : A) {m : ℕ} (hm : 0 < m) :
    deningerBigWittLogGhost (deningerBigWittFactor a m)
      (deningerBigWittFactor_constantCoeff a m hm.ne') =
      PowerSeries.C ((m : A) * a) * PowerSeries.X ^ m *
        deningerBigWittGeom a m := by
  rw [deningerBigWittLogGhost, deningerBigWittInvFactor_eq_geom a hm]
  rw [deningerBigWittDerivative_factor a hm]
  have hm_eq : m - 1 + 1 = m := Nat.sub_add_cancel hm
  calc
    -(PowerSeries.X * -(PowerSeries.C ((m : A) * a) *
        PowerSeries.X ^ (m - 1)) * deningerBigWittGeom a m) =
        PowerSeries.C ((m : A) * a) *
          (PowerSeries.X ^ (m - 1) * PowerSeries.X) *
            deningerBigWittGeom a m := by ring
    _ = _ := by rw [← pow_succ, hm_eq]

/-- Exact integral ghost component of one Euler factor. -/
theorem deningerBigWittLogGhost_factor_coeff
    (a : A) {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    PowerSeries.coeff k
      (deningerBigWittLogGhost (deningerBigWittFactor a m)
        (deningerBigWittFactor_constantCoeff a m hm.ne')) =
      if m ∣ k then (m : A) * a ^ (k / m) else 0 := by
  rw [deningerBigWittLogGhost_factor a hm, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hd : m ∣ k
  · rw [if_pos hd, if_pos (Nat.le_of_dvd hk hd), deningerBigWittGeom_coeff]
    obtain ⟨q, hq⟩ := hd
    have hq0 : q ≠ 0 := by
      intro h
      subst q
      apply hk.ne'
      simpa using hq
    rw [hq]
    have hsubeq : m * q - m = m * (q - 1) := by
      calc
        m * q - m = m * q - m * 1 := by rw [mul_one]
        _ = m * (q - 1) := (Nat.mul_sub_left_distrib m q 1).symm
    rw [hsubeq, if_pos (dvd_mul_right m (q - 1)),
      Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel_left _ hm]
    have hqeq : q = (q - 1) + 1 := by omega
    conv_rhs => rw [hqeq, pow_succ]
    ring
  · rw [if_neg hd]
    by_cases hle : m ≤ k
    · rw [if_pos hle, deningerBigWittGeom_coeff]
      have hsub : ¬m ∣ k - m := by
        intro hs
        apply hd
        rw [← Nat.sub_add_cancel hle]
        exact dvd_add hs (dvd_refl m)
      rw [if_neg hsub]
      simp
    · rw [if_neg hle]
      simp

/-- Coefficient `N` of the inverse of a constant-one series depends only on coefficients through
degree `N`. -/
theorem deningerBigWittInvOfUnit_coeff_congr
    {f g : PowerSeries A} {N : ℕ}
    (h : ∀ n ≤ N, PowerSeries.coeff n f = PowerSeries.coeff n g) :
    PowerSeries.coeff N (PowerSeries.invOfUnit f 1) =
      PowerSeries.coeff N (PowerSeries.invOfUnit g 1) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      rw [PowerSeries.coeff_invOfUnit, PowerSeries.coeff_invOfUnit]
      by_cases hN : N = 0
      · simp [hN]
      · rw [if_neg hN, if_neg hN]
        apply congrArg (fun z : A => -(1 : A) * z)
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hpN : p.2 < N
        · rw [if_pos hpN, if_pos hpN, h p.1]
          · congr 1
            exact ih p.2 hpN (fun n hn => h n (hn.trans (Nat.le_of_lt hpN)))
          · have hpEq := Finset.mem_antidiagonal.mp hp
            omega
        · rw [if_neg hpN, if_neg hpN]

/-- A logarithmic ghost coefficient through degree `N` depends only on the input coefficients
through degree `N`. -/
theorem deningerBigWittLogGhost_coeff_congr
    {f g : PowerSeries A}
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1)
    {N : ℕ}
    (h : ∀ n ≤ N, PowerSeries.coeff n f = PowerSeries.coeff n g) :
    PowerSeries.coeff N (deningerBigWittLogGhost f hf) =
      PowerSeries.coeff N (deningerBigWittLogGhost g hg) := by
  change -PowerSeries.coeff N
      (PowerSeries.X * PowerSeries.derivative A f * PowerSeries.invOfUnit f 1) =
    -PowerSeries.coeff N
      (PowerSeries.X * PowerSeries.derivative A g * PowerSeries.invOfUnit g 1)
  apply neg_injective
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  simp only [neg_neg]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  · rw [← pow_one PowerSeries.X]
    rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
    by_cases hp1 : 1 ≤ p.1
    · rw [if_pos hp1, if_pos hp1, PowerSeries.coeff_derivative,
        PowerSeries.coeff_derivative]
      have heq : p.1 - 1 + 1 = p.1 := Nat.sub_add_cancel hp1
      have hpLe : p.1 ≤ N := by
        have hpEq := Finset.mem_antidiagonal.mp hp
        omega
      rw [heq, h p.1 hpLe]
    · rw [if_neg hp1, if_neg hp1]
  · apply deningerBigWittInvOfUnit_coeff_congr
    intro n hn
    have hpLe : p.2 ≤ N := by
      have hpEq := Finset.mem_antidiagonal.mp hp
      omega
    exact h n (hn.trans hpLe)

theorem deningerBigWittLogGhost_pow
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) (d : ℕ) :
    deningerBigWittLogGhost (f ^ d) (by simp [hf]) =
      d • deningerBigWittLogGhost f hf := by
  induction d with
  | zero => simp [deningerBigWittLogGhost]
  | succ d ih =>
      calc
        deningerBigWittLogGhost (f ^ (d + 1)) (by simp [hf]) =
            deningerBigWittLogGhost (f ^ d * f) (by simp [hf]) :=
              deningerBigWittLogGhost_congr _ _ (pow_succ f d)
        _ =
            deningerBigWittLogGhost (f ^ d) (by simp [hf]) +
              deningerBigWittLogGhost f hf := by
                exact deningerBigWittLogGhost_mul (f ^ d) f (by simp [hf]) hf
        _ = (d + 1) • deningerBigWittLogGhost f hf := by rw [ih, succ_nsmul]

theorem deningerBigWittLogGhost_finset_prod
    {ι : Type*} (s : Finset ι) (F : ι → PowerSeries A)
    (hF : ∀ i, PowerSeries.constantCoeff (F i) = 1) :
    deningerBigWittLogGhost (∏ i ∈ s, F i)
        (by simp [hF]) =
      ∑ i ∈ s, deningerBigWittLogGhost (F i) (hF i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [deningerBigWittLogGhost]
  | @insert i s hi ih =>
      calc
        deningerBigWittLogGhost (∏ j ∈ insert i s, F j) (by simp [hF]) =
            deningerBigWittLogGhost (F i * ∏ j ∈ s, F j) (by simp [hF]) :=
              deningerBigWittLogGhost_congr _ _ (Finset.prod_insert hi)
        _ =
            deningerBigWittLogGhost (F i) (hF i) +
              deningerBigWittLogGhost (∏ j ∈ s, F j) (by simp [hF]) := by
                exact deningerBigWittLogGhost_mul (F i) (∏ j ∈ s, F j)
                  (hF i) (by simp [hF])
        _ = ∑ j ∈ insert i s, deningerBigWittLogGhost (F j) (hF j) := by
              rw [ih, Finset.sum_insert hi]

theorem deningerBigWittPairFactor_ghost_coeff
    (x y : ℕ → A) (i j : ℕ) {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff k
      (deningerBigWittLogGhost (deningerBigWittPairFactor x y i j)
        (deningerBigWittPairFactor_constantCoeff x y i j)) =
      if (i + 1).lcm (j + 1) ∣ k then
        ((i + 1).gcd (j + 1) : ℕ) •
          (((i + 1).lcm (j + 1) : A) *
            (x i ^ ((i + 1).lcm (j + 1) / (i + 1)) *
              y j ^ ((i + 1).lcm (j + 1) / (j + 1))) ^
                (k / ((i + 1).lcm (j + 1))))
      else 0 := by
  let m := i + 1
  let n := j + 1
  let l := m.lcm n
  let c := x i ^ (l / m) * y j ^ (l / n)
  change PowerSeries.coeff k
      (deningerBigWittLogGhost (deningerBigWittFactor c l ^ (m.gcd n))
        (by simp [deningerBigWittFactor_constantCoeff, m, n, l])) = _
  rw [deningerBigWittLogGhost_pow (deningerBigWittFactor c l)
    (deningerBigWittFactor_constantCoeff c l
      (Nat.lcm_pos (Nat.succ_pos i) (Nat.succ_pos j)).ne')]
  simp only [map_nsmul]
  rw [deningerBigWittLogGhost_factor_coeff c
    (Nat.lcm_pos (Nat.succ_pos i) (Nat.succ_pos j)) hk]
  simp only [m, n, l, c]
  split_ifs <;> simp

theorem deningerBigWittPairPartial_ghost
    (x y : ℕ → A) (N : ℕ) :
    deningerBigWittLogGhost (deningerBigWittPairPartial x y N)
        (deningerBigWittPairPartial_constantCoeff x y N) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        deningerBigWittLogGhost (deningerBigWittPairFactor x y i j)
          (deningerBigWittPairFactor_constantCoeff x y i j) := by
  calc
    deningerBigWittLogGhost (deningerBigWittPairPartial x y N)
        (deningerBigWittPairPartial_constantCoeff x y N) =
      ∑ i ∈ Finset.range N,
        deningerBigWittLogGhost
          (∏ j ∈ Finset.range N, deningerBigWittPairFactor x y i j)
          (by simp) := by
            exact deningerBigWittLogGhost_finset_prod (Finset.range N)
              (fun i => ∏ j ∈ Finset.range N, deningerBigWittPairFactor x y i j)
              (fun i => by simp)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact deningerBigWittLogGhost_finset_prod (Finset.range N)
        (fun j => deningerBigWittPairFactor x y i j)
        (fun j => deningerBigWittPairFactor_constantCoeff x y i j)

theorem deningerBigWittEulerPartial_ghost
    (x : ℕ → A) (N : ℕ) :
    deningerBigWittLogGhost (deningerBigWittEulerPartial x N)
        (deningerBigWittEulerPartial_constantCoeff x N) =
      ∑ i ∈ Finset.range N,
        deningerBigWittLogGhost (deningerBigWittFactor (x i) (i + 1))
          (deningerBigWittFactor_constantCoeff (x i) (i + 1)
            (Nat.succ_ne_zero i)) := by
  unfold deningerBigWittEulerPartial
  exact deningerBigWittLogGhost_finset_prod (Finset.range N)
    (fun i => deningerBigWittFactor (x i) (i + 1))
    (fun i => deningerBigWittFactor_constantCoeff (x i) (i + 1)
      (Nat.succ_ne_zero i))

/-- Positive-degree ghost component in Euler coordinates. -/
def deningerBigWittEulerGhost (x : ℕ → A) (k : ℕ) : A :=
  ∑ i ∈ Finset.range k,
    if i + 1 ∣ k then ((i + 1 : ℕ) : A) * x i ^ (k / (i + 1)) else 0

theorem deningerBigWittEulerSeries_ghost_coeff
    (x : ℕ → A) {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff k
      (deningerBigWittLogGhost (deningerBigWittEulerSeries x)
        (deningerBigWittEulerSeries_constantCoeff x)) =
      deningerBigWittEulerGhost x k := by
  rw [deningerBigWittLogGhost_coeff_congr
    (deningerBigWittEulerSeries_constantCoeff x)
    (deningerBigWittEulerPartial_constantCoeff x k)
    (fun n hn => by
      rw [deningerBigWittEulerSeries_coeff]
      exact (deningerBigWittEulerPartial_coeff_stable x le_rfl hn).symm)]
  rw [deningerBigWittEulerPartial_ghost]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [deningerBigWittLogGhost_factor_coeff (x i) (Nat.succ_pos i) hk]

theorem deningerBigWittPairGhostTerm_eq_mul
    (a b : A) {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (if m.lcm n ∣ k then
      (m.gcd n) • (((m.lcm n : ℕ) : A) *
        (a ^ (m.lcm n / m) * b ^ (m.lcm n / n)) ^ (k / m.lcm n))
    else 0) =
      (if m ∣ k then (m : A) * a ^ (k / m) else 0) *
        (if n ∣ k then (n : A) * b ^ (k / n) else 0) := by
  by_cases hL : m.lcm n ∣ k
  · rw [if_pos hL, if_pos ((Nat.dvd_lcm_left m n).trans hL),
      if_pos ((Nat.dvd_lcm_right m n).trans hL)]
    obtain ⟨q, hq⟩ := hL
    rw [hq, Nat.mul_div_cancel_left _ (Nat.lcm_pos hm hn)]
    have hmL : m * (m.lcm n / m) = m.lcm n :=
      Nat.mul_div_cancel' (Nat.dvd_lcm_left m n)
    have hnL : n * (m.lcm n / n) = m.lcm n :=
      Nat.mul_div_cancel' (Nat.dvd_lcm_right m n)
    have hkm : m.lcm n * q / m = (m.lcm n / m) * q := by
      calc
        m.lcm n * q / m = (m * (m.lcm n / m) * q) / m := by rw [hmL]
        _ = (m * ((m.lcm n / m) * q)) / m := by rw [Nat.mul_assoc]
        _ = (m.lcm n / m) * q := Nat.mul_div_cancel_left _ hm
    have hkn : m.lcm n * q / n = (m.lcm n / n) * q := by
      calc
        m.lcm n * q / n = (n * (m.lcm n / n) * q) / n := by rw [hnL]
        _ = (n * ((m.lcm n / n) * q)) / n := by rw [Nat.mul_assoc]
        _ = (m.lcm n / n) * q := Nat.mul_div_cancel_left _ hn
    rw [hkm, hkn, mul_pow, pow_mul, pow_mul, nsmul_eq_mul]
    have hgcd : ((m.gcd n : ℕ) : A) * (m.lcm n : A) =
        (m : A) * (n : A) := by
      simpa only [Nat.cast_mul] using
        congrArg (fun z : ℕ => (z : A)) (Nat.gcd_mul_lcm m n)
    rw [← mul_assoc, hgcd]
    ring
  · rw [if_neg hL]
    have hnot : ¬(m ∣ k ∧ n ∣ k) := by
      simpa [Nat.lcm_dvd_iff] using hL
    rcases not_and_or.mp hnot with hmK | hnK
    · rw [if_neg hmK]
      simp
    · rw [if_neg hnK]
      simp

/-- The finite pair product has componentwise multiplicative ghost coordinates. -/
theorem deningerBigWittPairPartial_ghost_coeff
    (x y : ℕ → A) {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff k
      (deningerBigWittLogGhost (deningerBigWittPairPartial x y k)
        (deningerBigWittPairPartial_constantCoeff x y k)) =
      deningerBigWittEulerGhost x k * deningerBigWittEulerGhost y k := by
  rw [deningerBigWittPairPartial_ghost]
  simp only [map_sum]
  rw [deningerBigWittEulerGhost, deningerBigWittEulerGhost,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [deningerBigWittPairFactor_ghost_coeff x y i j hk]
  exact deningerBigWittPairGhostTerm_eq_mul (x i) (y j)
    (Nat.succ_pos i) (Nat.succ_pos j)

/-- The completed integral pair product has multiplicative ghost components.  Completion is
handled coefficientwise; no division by integers and no injectivity in the target ring occur. -/
theorem deningerBigWittMulSeries_ghost_coeff
    (x y : ℕ → A) {k : ℕ} (hk : 0 < k) :
    PowerSeries.coeff k
      (deningerBigWittLogGhost (deningerBigWittMulSeries x y)
        (deningerBigWittMulSeries_constantCoeff x y)) =
      deningerBigWittEulerGhost x k * deningerBigWittEulerGhost y k := by
  rw [deningerBigWittLogGhost_coeff_congr
    (deningerBigWittMulSeries_constantCoeff x y)
    (deningerBigWittPairPartial_constantCoeff x y k)
    (fun n hn => by
      rw [deningerBigWittMulSeries_coeff]
      exact (deningerBigWittPairPartial_coeff_stable x y le_rfl hn).symm)]
  exact deningerBigWittPairPartial_ghost_coeff x y hk

/-- Ghost series on the literal big-Witt carrier. -/
def deningerBigWittGhostSeries (w : DeningerBigWittAdditive A) : PowerSeries A :=
  deningerBigWittLogGhost (deningerBigWittSeries w)
    (deningerBigWittSeries_constantCoeff w)

/-- Ghost component indexed by a positive integer. -/
def deningerBigWittGhostCoeff (w : DeningerBigWittAdditive A) (k : ℕ) : A :=
  PowerSeries.coeff k (deningerBigWittGhostSeries w)

theorem deningerBigWittGhostCoeff_euler
    (x : ℕ → A) {k : ℕ} (hk : 0 < k) :
    deningerBigWittGhostCoeff (deningerBigWittEulerEquiv A x) k =
      deningerBigWittEulerGhost x k := by
  exact deningerBigWittEulerSeries_ghost_coeff x hk

/-- Defining ghost law for canonical big-Witt multiplication, proved integrally over every
commutative ring. -/
theorem deningerBigWittGhostCoeff_mul
    (u v : DeningerBigWittAdditive A) {k : ℕ} (hk : 0 < k) :
    deningerBigWittGhostCoeff (deningerBigWittMul u v) k =
      deningerBigWittGhostCoeff u k * deningerBigWittGhostCoeff v k := by
  change PowerSeries.coeff k
      (deningerBigWittLogGhost
        (deningerBigWittMulSeries
          ((deningerBigWittEulerEquiv A).symm u)
          ((deningerBigWittEulerEquiv A).symm v))
        (deningerBigWittMulSeries_constantCoeff _ _)) = _
  rw [deningerBigWittMulSeries_ghost_coeff _ _ hk]
  rw [← deningerBigWittGhostCoeff_euler
    ((deningerBigWittEulerEquiv A).symm u) hk]
  rw [← deningerBigWittGhostCoeff_euler
    ((deningerBigWittEulerEquiv A).symm v) hk]
  congr 1
  · exact congrArg (fun w => deningerBigWittGhostCoeff w k)
      ((deningerBigWittEulerEquiv A).apply_symm_apply u)
  · exact congrArg (fun w => deningerBigWittGhostCoeff w k)
      ((deningerBigWittEulerEquiv A).apply_symm_apply v)

@[simp] theorem deningerBigWittGhostSeries_one :
    deningerBigWittGhostSeries (1 : DeningerBigWittAdditive A) = 0 := by
  simp [deningerBigWittGhostSeries, deningerBigWittLogGhost, deningerBigWittSeries]

@[simp] theorem deningerBigWittGhostSeries_mul
    (u v : DeningerBigWittAdditive A) :
    deningerBigWittGhostSeries (u * v) =
      deningerBigWittGhostSeries u + deningerBigWittGhostSeries v := by
  exact deningerBigWittLogGhost_mul _ _ _ _

theorem deningerBigWittLogGhost_eq_iff
    [IsAddTorsionFree A]
    {f g : PowerSeries A}
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    deningerBigWittLogGhost f hf = deningerBigWittLogGhost g hg ↔ f = g := by
  constructor
  · intro h
    let fi : PowerSeries A := PowerSeries.invOfUnit f 1
    let gi : PowerSeries A := PowerSeries.invOfUnit g 1
    have hfi : f * fi = 1 := PowerSeries.mul_invOfUnit f 1 hf
    have hif : fi * f = 1 := PowerSeries.invOfUnit_mul f 1 hf
    have hgi : g * gi = 1 := PowerSeries.mul_invOfUnit g 1 hg
    have hlog : PowerSeries.derivative A f * fi =
        PowerSeries.derivative A g * gi := by
      have hx : -(PowerSeries.X * (PowerSeries.derivative A f * fi)) =
          -(PowerSeries.X * (PowerSeries.derivative A g * gi)) := by
        simpa only [deningerBigWittLogGhost, fi, gi, mul_assoc] using h
      have hx' : PowerSeries.X * (PowerSeries.derivative A f * fi) =
          PowerSeries.X * (PowerSeries.derivative A g * gi) := neg_injective hx
      exact PowerSeries.X_pow_mul_injective (k := 1) (by simpa using hx')
    have hD : PowerSeries.derivative A (f * gi) = 0 := by
      change PowerSeries.derivativeFun (f * gi) = 0
      rw [PowerSeries.derivativeFun_mul]
      simp only [smul_eq_mul]
      have hginv : PowerSeries.derivative A gi =
          -(gi ^ 2) * PowerSeries.derivative A g := by
        have hu : IsUnit g := PowerSeries.isUnit_iff_constantCoeff.mpr (hg ▸ isUnit_one)
        have hunit : hu.unit = (⟨g, gi, PowerSeries.mul_invOfUnit g 1 hg,
            PowerSeries.invOfUnit_mul g 1 hg⟩ : (PowerSeries A)ˣ) := by
          apply Units.ext
          rfl
        have hd := PowerSeries.derivative_inv hu.unit
        rw [hunit] at hd
        exact hd
      change f * PowerSeries.derivative A gi + gi * PowerSeries.derivative A f = 0
      rw [hginv]
      have hlog' : PowerSeries.derivative A f =
          PowerSeries.derivative A g * gi * f := by
        calc
          PowerSeries.derivative A f =
              (PowerSeries.derivative A f * fi) * f := by rw [mul_assoc, hif, mul_one]
          _ = PowerSeries.derivative A g * gi * f := by rw [hlog]
      rw [hlog']
      rw [pow_two]
      ring
    have hc : PowerSeries.constantCoeff (f * gi) =
        PowerSeries.constantCoeff (1 : PowerSeries A) := by
      simp [gi, hf]
    have hD' : PowerSeries.derivative A (f * gi) =
        PowerSeries.derivative A (1 : PowerSeries A) := by simpa using hD
    have hquot : f * gi = 1 := PowerSeries.derivative.ext hD' hc
    calc
      f = (f * gi) * g := by rw [mul_assoc, PowerSeries.invOfUnit_mul g 1 hg, mul_one]
      _ = g := by rw [hquot, one_mul]
  · exact fun h => h ▸ rfl

/-- Ghost injectivity over additively torsion-free rings. -/
theorem deningerBigWittGhostSeries_injective [IsAddTorsionFree A] :
    Function.Injective (deningerBigWittGhostSeries (A := A)) := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  exact (deningerBigWittLogGhost_eq_iff
    (deningerBigWittSeries_constantCoeff u)
    (deningerBigWittSeries_constantCoeff v)).mp huv

end

end RHTower
