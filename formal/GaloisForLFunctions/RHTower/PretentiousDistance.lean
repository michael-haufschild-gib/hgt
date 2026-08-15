import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp

/-!
# The pretentious prime-clock distance

For unimodular-bounded prime data the squared distance

```text
D_x(f,g)² = ∑_{p ≤ x} (1 - Re(f(p) conj(g(p))))/p
```

is a metric: the local quantity `1 - Re(u conj v)` obeys a square-root triangle inequality on the
closed unit disc, which the Cauchy–Schwarz inequality lifts to the weighted prime sum.  Reflecting
a real prime sequence through a character costs exactly the factor four:

```text
D_x(n^{-iα}, n^{iα})² ≤ 4 D_x(g, n^{iα})²      for real `g`.
```
-/

open Filter Topology Finset

namespace RHTower

noncomputable section

/-- The local pretentious distance `1 - Re(u conj v)` on the closed unit disc. -/
def unitDiskDist (u v : ℂ) : ℝ := 1 - (u * (starRingEnd ℂ) v).re

theorem unitDiskDist_eq (u v : ℂ) :
    unitDiskDist u v
      = (‖u - v‖ ^ 2 + (1 - ‖u‖ ^ 2) + (1 - ‖v‖ ^ 2)) / 2 := by
  have hnorm : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (u * (starRingEnd ℂ) v).re := by
    have h := Complex.normSq_sub u v
    have hu : ‖u‖ ^ 2 = Complex.normSq u := Complex.sq_norm u
    have hv : ‖v‖ ^ 2 = Complex.normSq v := Complex.sq_norm v
    have huv : ‖u - v‖ ^ 2 = Complex.normSq (u - v) := Complex.sq_norm (u - v)
    rw [huv, hu, hv, h]
  rw [unitDiskDist, hnorm]
  ring

theorem unitDiskDist_nonneg {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    0 ≤ unitDiskDist u v := by
  rw [unitDiskDist_eq]
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith
  have h2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith
  have h3 : (0 : ℝ) ≤ ‖u - v‖ ^ 2 := sq_nonneg _
  linarith

theorem norm_sub_sq_le_two_mul_unitDiskDist {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖u - v‖ ^ 2 ≤ 2 * unitDiskDist u v := by
  rw [unitDiskDist_eq]
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith
  have h2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith
  linarith

/-- **The local pretentious triangle inequality on the closed unit disc.** -/
theorem sqrt_unitDiskDist_triangle {u v w : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    Real.sqrt (unitDiskDist u v)
      ≤ Real.sqrt (unitDiskDist u w) + Real.sqrt (unitDiskDist w v) := by
  have ha := unitDiskDist_nonneg hu hw
  have hb := unitDiskDist_nonneg hw hv
  have hc := unitDiskDist_nonneg hu hv
  -- the algebraic identity `c - a - b = Re[(u-w)(conj w - conj v)] + ‖w‖² - 1`
  have hkey : unitDiskDist u v - unitDiskDist u w - unitDiskDist w v
      = ((u - w) * ((starRingEnd ℂ) w - (starRingEnd ℂ) v)).re + ‖w‖ ^ 2 - 1 := by
    have hw2 : ‖w‖ ^ 2 = (w * (starRingEnd ℂ) w).re := by
      rw [Complex.mul_conj, Complex.sq_norm]
      simp
    simp only [unitDiskDist, hw2, mul_sub, sub_mul, Complex.sub_re]
    ring
  have hwsq : ‖w‖ ^ 2 ≤ 1 := by
    have : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
    nlinarith
  have hre : ((u - w) * ((starRingEnd ℂ) w - (starRingEnd ℂ) v)).re
      ≤ ‖u - w‖ * ‖w - v‖ := by
    have h := Complex.re_le_norm ((u - w) * ((starRingEnd ℂ) w - (starRingEnd ℂ) v))
    have hnorm : ‖(u - w) * ((starRingEnd ℂ) w - (starRingEnd ℂ) v)‖ = ‖u - w‖ * ‖w - v‖ := by
      rw [norm_mul]
      congr 1
      rw [← map_sub, RCLike.norm_conj]
    rw [hnorm] at h
    exact h
  have huw : ‖u - w‖ ≤ Real.sqrt (2 * unitDiskDist u w) := by
    have h := norm_sub_sq_le_two_mul_unitDiskDist hu hw
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hwv : ‖w - v‖ ≤ Real.sqrt (2 * unitDiskDist w v) := by
    have h := norm_sub_sq_le_two_mul_unitDiskDist hw hv
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hprod : ‖u - w‖ * ‖w - v‖
      ≤ 2 * (Real.sqrt (unitDiskDist u w) * Real.sqrt (unitDiskDist w v)) := by
    have hle : ‖u - w‖ * ‖w - v‖
        ≤ Real.sqrt (2 * unitDiskDist u w) * Real.sqrt (2 * unitDiskDist w v) :=
      mul_le_mul huw hwv (norm_nonneg _) (Real.sqrt_nonneg _)
    have hval : Real.sqrt (2 * unitDiskDist u w) * Real.sqrt (2 * unitDiskDist w v)
        = 2 * (Real.sqrt (unitDiskDist u w) * Real.sqrt (unitDiskDist w v)) := by
      rw [Real.sqrt_mul (by norm_num) , Real.sqrt_mul (by norm_num),
        show Real.sqrt 2 * Real.sqrt (unitDiskDist u w)
          * (Real.sqrt 2 * Real.sqrt (unitDiskDist w v))
          = (Real.sqrt 2 * Real.sqrt 2)
            * (Real.sqrt (unitDiskDist u w) * Real.sqrt (unitDiskDist w v)) by ring,
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [hval] at hle
    exact hle
  have hcle : unitDiskDist u v
      ≤ unitDiskDist u w + unitDiskDist w v
        + 2 * (Real.sqrt (unitDiskDist u w) * Real.sqrt (unitDiskDist w v)) := by
    linarith [hkey, hre, hprod, hwsq]
  have hsq : unitDiskDist u v
      ≤ (Real.sqrt (unitDiskDist u w) + Real.sqrt (unitDiskDist w v)) ^ 2 := by
    have hA : Real.sqrt (unitDiskDist u w) ^ 2 = unitDiskDist u w := Real.sq_sqrt ha
    have hB : Real.sqrt (unitDiskDist w v) ^ 2 = unitDiskDist w v := Real.sq_sqrt hb
    nlinarith [hcle, hA, hB]
  have hsum : 0 ≤ Real.sqrt (unitDiskDist u w) + Real.sqrt (unitDiskDist w v) := by
    positivity
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hsum] at this

/-! ## The prime-weighted distance -/

/-- The squared pretentious distance `∑_{p ≤ x} (1 - Re(f(p) conj(g(p))))/p`. -/
def pretentiousDistSq (f g : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, unitDiskDist (f p) (g p) / p

theorem pretentiousDistSq_nonneg {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (x : ℝ) : 0 ≤ pretentiousDistSq f g x := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  exact div_nonneg (unitDiskDist_nonneg (hf p) (hg p)) hp0.le

/-- Minkowski's inequality for finite sums, in square-root form. -/
theorem sqrt_sum_le_of_sqrt_le {ι : Type*} {s : Finset ι} {A B C : ι → ℝ}
    (hA : ∀ i ∈ s, 0 ≤ A i) (hB : ∀ i ∈ s, 0 ≤ B i) (hC0 : ∀ i ∈ s, 0 ≤ C i)
    (hC : ∀ i ∈ s, Real.sqrt (C i) ≤ Real.sqrt (A i) + Real.sqrt (B i)) :
    Real.sqrt (∑ i ∈ s, C i) ≤ Real.sqrt (∑ i ∈ s, A i) + Real.sqrt (∑ i ∈ s, B i) := by
  have hAsum : 0 ≤ ∑ i ∈ s, A i := Finset.sum_nonneg hA
  have hBsum : 0 ≤ ∑ i ∈ s, B i := Finset.sum_nonneg hB
  have hcs : (∑ i ∈ s, Real.sqrt (A i) * Real.sqrt (B i)) ^ 2
      ≤ (∑ i ∈ s, A i) * (∑ i ∈ s, B i) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (A i))
      (fun i => Real.sqrt (B i))
    have hA' : ∑ i ∈ s, Real.sqrt (A i) ^ 2 = ∑ i ∈ s, A i :=
      Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hA i hi)
    have hB' : ∑ i ∈ s, Real.sqrt (B i) ^ 2 = ∑ i ∈ s, B i :=
      Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hB i hi)
    rwa [hA', hB'] at h
  have hcsroot : ∑ i ∈ s, Real.sqrt (A i) * Real.sqrt (B i)
      ≤ Real.sqrt (∑ i ∈ s, A i) * Real.sqrt (∑ i ∈ s, B i) := by
    have hnn : 0 ≤ Real.sqrt (∑ i ∈ s, A i) * Real.sqrt (∑ i ∈ s, B i) := by positivity
    have hsq : (Real.sqrt (∑ i ∈ s, A i) * Real.sqrt (∑ i ∈ s, B i)) ^ 2
        = (∑ i ∈ s, A i) * (∑ i ∈ s, B i) := by
      rw [mul_pow, Real.sq_sqrt hAsum, Real.sq_sqrt hBsum]
    nlinarith [hcs, hnn, hsq, Finset.sum_nonneg (fun i (hi : i ∈ s) =>
      mul_nonneg (Real.sqrt_nonneg (A i)) (Real.sqrt_nonneg (B i)))]
  have hterm : ∑ i ∈ s, C i
      ≤ ∑ i ∈ s, (A i + B i + 2 * (Real.sqrt (A i) * Real.sqrt (B i))) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hloc := hC i hi
    have hAi : Real.sqrt (A i) ^ 2 = A i := Real.sq_sqrt (hA i hi)
    have hBi : Real.sqrt (B i) ^ 2 = B i := Real.sq_sqrt (hB i hi)
    have hCi : Real.sqrt (C i) ^ 2 = C i := Real.sq_sqrt (hC0 i hi)
    nlinarith [hloc, hAi, hBi, hCi, Real.sqrt_nonneg (A i), Real.sqrt_nonneg (B i),
      Real.sqrt_nonneg (C i)]
  have hsplit : ∑ i ∈ s, (A i + B i + 2 * (Real.sqrt (A i) * Real.sqrt (B i)))
      = (∑ i ∈ s, A i) + (∑ i ∈ s, B i)
        + 2 * ∑ i ∈ s, Real.sqrt (A i) * Real.sqrt (B i) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hfinal : ∑ i ∈ s, C i
      ≤ (Real.sqrt (∑ i ∈ s, A i) + Real.sqrt (∑ i ∈ s, B i)) ^ 2 := by
    have hA' : Real.sqrt (∑ i ∈ s, A i) ^ 2 = ∑ i ∈ s, A i := Real.sq_sqrt hAsum
    have hB' : Real.sqrt (∑ i ∈ s, B i) ^ 2 = ∑ i ∈ s, B i := Real.sq_sqrt hBsum
    nlinarith [hterm, hsplit.le, hsplit.ge, hcsroot, hA', hB']
  have hsum : 0 ≤ Real.sqrt (∑ i ∈ s, A i) + Real.sqrt (∑ i ∈ s, B i) := by positivity
  have := Real.sqrt_le_sqrt hfinal
  rwa [Real.sqrt_sq hsum] at this

/-- **The pretentious triangle inequality.** -/
theorem sqrt_pretentiousDistSq_triangle {f g h : ℕ → ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (hh : ∀ n, ‖h n‖ ≤ 1) (x : ℝ) :
    Real.sqrt (pretentiousDistSq f g x)
      ≤ Real.sqrt (pretentiousDistSq f h x) + Real.sqrt (pretentiousDistSq h g x) := by
  rw [pretentiousDistSq, pretentiousDistSq, pretentiousDistSq]
  refine sqrt_sum_le_of_sqrt_le ?_ ?_ ?_ ?_ <;> intro p hp
  · have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    exact div_nonneg (unitDiskDist_nonneg (hf p) (hh p)) hp0.le
  · have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    exact div_nonneg (unitDiskDist_nonneg (hh p) (hg p)) hp0.le
  · have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    exact div_nonneg (unitDiskDist_nonneg (hf p) (hg p)) hp0.le
  · have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hloc := sqrt_unitDiskDist_triangle (hf p) (hg p) (hh p)
    have hdiv : ∀ c : ℝ, 0 ≤ c → Real.sqrt (c / p) = Real.sqrt c / Real.sqrt p := fun c hc =>
      Real.sqrt_div hc _
    rw [hdiv _ (unitDiskDist_nonneg (hf p) (hg p)), hdiv _ (unitDiskDist_nonneg (hf p) (hh p)),
      hdiv _ (unitDiskDist_nonneg (hh p) (hg p)), ← add_div]
    exact div_le_div_of_nonneg_right hloc (Real.sqrt_pos.mpr hp0).le

/-! ## Characters and the real reflection -/

/-- The archimedean character `n ↦ n^{iα}`. -/
def primeChar (α : ℝ) (n : ℕ) : ℂ := Complex.exp ((α * Real.log n : ℝ) * Complex.I)

theorem norm_primeChar (α : ℝ) (n : ℕ) : ‖primeChar α n‖ = 1 := by
  rw [primeChar, Complex.norm_exp]
  simp

theorem norm_primeChar_le_one (α : ℝ) (n : ℕ) : ‖primeChar α n‖ ≤ 1 := by
  rw [norm_primeChar]

theorem unitDiskDist_primeChar (α : ℝ) (n : ℕ) :
    unitDiskDist (primeChar (-α) n) (primeChar α n)
      = 1 - Real.cos (2 * α * Real.log n) := by
  rw [unitDiskDist, primeChar, primeChar, ← Complex.exp_conj]
  have hconj : (starRingEnd ℂ) ((↑(α * Real.log n) : ℂ) * Complex.I)
      = -((↑(α * Real.log n) : ℂ) * Complex.I) := by
    simp [Complex.ext_iff]
  rw [hconj, ← Complex.exp_add]
  have harg : (↑(-α * Real.log n) : ℂ) * Complex.I + -((↑(α * Real.log n) : ℂ) * Complex.I)
      = (↑(-(2 * α * Real.log n)) : ℝ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The squared distance between the two conjugate characters is the cosine defect. -/
theorem pretentiousDistSq_primeChar (α x : ℝ) :
    pretentiousDistSq (primeChar (-α)) (primeChar α) x
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - Real.cos (2 * α * Real.log p)) / p := by
  rw [pretentiousDistSq]
  exact Finset.sum_congr rfl fun p _ => by rw [unitDiskDist_primeChar]

/-- **The real reflection identity.**  A real prime sequence is equidistant from a character and
from its conjugate. -/
theorem pretentiousDistSq_real_reflect {r : ℕ → ℝ} (α x : ℝ) :
    pretentiousDistSq (primeChar (-α)) (fun n => (r n : ℂ)) x
      = pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x := by
  rw [pretentiousDistSq, pretentiousDistSq]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [unitDiskDist, unitDiskDist, primeChar, primeChar]
  have hconj : (starRingEnd ℂ) ((↑(α * Real.log p) : ℂ) * Complex.I)
      = -((↑(α * Real.log p) : ℂ) * Complex.I) := by
    simp [Complex.ext_iff]
  rw [← Complex.exp_conj, hconj]
  have hleft : (Complex.exp ((↑(-α * Real.log p) : ℂ) * Complex.I)
      * (starRingEnd ℂ) (r p : ℂ)).re
      = r p * Real.cos (α * Real.log p) := by
    rw [Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hre : (Complex.exp ((↑(-α * Real.log p) : ℂ) * Complex.I)).re
        = Real.cos (-α * Real.log p) := Complex.exp_ofReal_mul_I_re _
    have him : (Complex.exp ((↑(-α * Real.log p) : ℂ) * Complex.I)).im
        = Real.sin (-α * Real.log p) := by
      rw [Complex.exp_ofReal_mul_I_im]
    rw [hre, him]
    have hcos : Real.cos (-α * Real.log p) = Real.cos (α * Real.log p) := by
      rw [show -α * Real.log p = -(α * Real.log p) by ring, Real.cos_neg]
    rw [hcos]
    ring
  have hright : ((r p : ℂ) * Complex.exp (-((↑(α * Real.log p) : ℂ) * Complex.I))).re
      = r p * Real.cos (α * Real.log p) := by
    have hneg : -((↑(α * Real.log p) : ℂ) * Complex.I)
        = (↑(-(α * Real.log p)) : ℝ) * Complex.I := by
      push_cast
      ring
    rw [hneg]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  rw [hleft, hright]

/-- **(Z10) The reflection costs exactly a factor four.**  For a real prime sequence in the closed
unit disc, the character separation is at most four times the pretentious distance. -/
theorem pretentiousDistSq_primeChar_le_four_mul {r : ℕ → ℝ}
    (hr : ∀ n, |r n| ≤ 1) (α x : ℝ) :
    pretentiousDistSq (primeChar (-α)) (primeChar α) x
      ≤ 4 * pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x := by
  have hnorm : ∀ n, ‖((r n : ℂ))‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real]
    exact hr n
  have htri := sqrt_pretentiousDistSq_triangle (f := primeChar (-α)) (g := primeChar α)
    (h := fun n => (r n : ℂ)) (fun n => norm_primeChar_le_one _ n)
    (fun n => norm_primeChar_le_one _ n) hnorm x
  rw [pretentiousDistSq_real_reflect (r := r)] at htri
  have hnn : 0 ≤ pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x :=
    pretentiousDistSq_nonneg hnorm (fun n => norm_primeChar_le_one _ n) x
  have hlhs : 0 ≤ pretentiousDistSq (primeChar (-α)) (primeChar α) x :=
    pretentiousDistSq_nonneg (fun n => norm_primeChar_le_one _ n)
      (fun n => norm_primeChar_le_one _ n) x
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) htri
  rw [Real.mul_self_sqrt hlhs] at hsq
  have hval : (Real.sqrt (pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x)
      + Real.sqrt (pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x))
      * (Real.sqrt (pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x)
        + Real.sqrt (pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x))
      = 4 * pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x := by
    have hs := Real.mul_self_sqrt hnn
    nlinarith [hs]
  rw [hval] at hsq
  exact hsq

end

end RHTower
