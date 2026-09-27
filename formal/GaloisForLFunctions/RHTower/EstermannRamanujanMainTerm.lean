import GaloisForLFunctions.RHTower.EstermannProgressionUniform

/-!
# The progression main term is a Ramanujan expansion

The smoothed divisor sum in the progression `N ≡ b (mod q)` has main term
`∑_{a mod q} e(−ab/q) · main(q / gcd(a, q))`.  Grouping the residues by their reduced modulus
`d = q / gcd(a, q)` turns this into a sum over divisors: the residues with reduced modulus `d` are
exactly `a = (q/d) m` with `0 ≤ m < d` and `gcd(m, d) = 1`, and for these `e(−ab/q) = e(−mb/d)`.
The inner sums are Ramanujan sums, which are even in `b`, so

`q ∑_{N ≡ b (q)} d(N) e^{−Nx} = ∑_{d ∣ q} c_d(b) · (γ − log x − 2 log d)/(dx) + O(q^{5/2} x^{−1/2})`

with an absolute implied constant.  The grouping is purely finite; no analysis enters.
-/

open Complex
open scoped Real

namespace RHTower

noncomputable section

/-- The Ramanujan sum `c_d(b) = ∑_{0 ≤ m < d, gcd(m, d) = 1} e(mb/d)`. -/
def estermannRamanujanSum (d : ℕ) (b : ℤ) : ℂ :=
  ∑ m ∈ (Finset.range d).filter (fun m => Nat.Coprime m d),
    Complex.exp (2 * π * I * ((m : ℂ) * (b : ℂ)) / (d : ℂ))

/-- A sum over `ZMod q` is the sum over the representatives `0 ≤ n < q`. -/
theorem sum_zmod_eq_sum_range (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    ∑ a : ZMod q, f a = ∑ n ∈ Finset.range q, f (n : ZMod q) := by
  refine Finset.sum_nbij' (fun a => a.val) (fun n => (n : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro n _
    exact Finset.mem_univ _
  · intro a _
    exact ZMod.natCast_zmod_val a
  · intro n hn
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)
  · intro a _
    rw [ZMod.natCast_zmod_val]

/-- The residues of reduced modulus `d` are the multiples `(q/d) m` with `m` a reduced residue
mod `d`. -/
theorem sum_filter_reducedModulus_eq (q : ℕ) (hq : q ≠ 0) {d : ℕ} (hd : d ∈ q.divisors)
    (F : ℕ → ℂ) :
    ∑ n ∈ (Finset.range q).filter (fun n => q / Nat.gcd n q = d), F n
      = ∑ m ∈ (Finset.range d).filter (fun m => Nat.Coprime m d), F (q / d * m) := by
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq
  set e : ℕ := q / d with he
  have hqed : q = e * d := by rw [he, Nat.div_mul_cancel hdq]
  have he0 : 0 < e := Nat.div_pos (Nat.le_of_dvd hq0 hdq) hd0
  -- the gcd of a fibre element is `e`
  have hgcd_of : ∀ n, q / Nat.gcd n q = d → Nat.gcd n q = e := by
    intro n hn
    have hgq : Nat.gcd n q ∣ q := Nat.gcd_dvd_right _ _
    have h1 : q = Nat.gcd n q * d := by
      rw [← hn, Nat.mul_div_cancel' hgq]
    rw [he]
    exact (Nat.div_eq_of_eq_mul_left hd0 h1).symm
  symm
  refine Finset.sum_nbij' (fun m => e * m) (fun n => n / e) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmd, hcop⟩ := hm
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · rw [hqed]
      exact Nat.mul_lt_mul_of_pos_left hmd he0
    · have hg : Nat.gcd (e * m) q = e := by
        rw [hqed, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop, mul_one]
      rw [hg, he, Nat.div_div_self hdq hq]
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnq, hnd⟩ := hn
    have hg := hgcd_of n hnd
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul he0, mul_comm d e, ← hqed]
      exact hnq
    · have hcop := Nat.coprime_div_gcd_div_gcd (m := n) (n := q)
        (Nat.gcd_pos_of_pos_right _ hq0)
      rw [hg] at hcop
      have hqe : q / e = d := by
        rw [hqed, Nat.mul_div_cancel_left _ he0]
      rw [hqe] at hcop
      exact hcop
  · intro m _
    exact Nat.mul_div_cancel_left m he0
  · intro n hn
    rw [Finset.mem_filter] at hn
    have hen : e ∣ n := (hgcd_of n hn.2) ▸ Nat.gcd_dvd_left n q
    exact Nat.mul_div_cancel' hen
  · intro m _
    rfl

/-- The additive character at a representative, as an exponential. -/
theorem stdAddChar_neg_natCast_mul (q : ℕ) [NeZero q] (n : ℕ) (b : ZMod q) :
    ((ZMod.stdAddChar (-((n : ZMod q) * b))) : ℂ)
      = Complex.exp (2 * π * I * ((n : ℂ) * ((-(b.val : ℤ) : ℤ) : ℂ)) / (q : ℂ)) := by
  have hcast : -((n : ZMod q) * b) = (((n : ℤ) * (-(b.val : ℤ)) : ℤ) : ZMod q) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  rw [hcast, ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- **Grouping by the reduced modulus.**  For any weight `g` on the moduli,
`∑_{a mod q} e(−ab/q) g(q/gcd(a,q)) = ∑_{d ∣ q} c_d(−b) g(d)`. -/
theorem sum_stdAddChar_mul_reducedModulus (q : ℕ) [NeZero q] (b : ZMod q) (g : ℕ → ℂ) :
    ∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) * g (reducedModulus q a)
      = ∑ d ∈ q.divisors, estermannRamanujanSum d (-(b.val : ℤ)) * g d := by
  classical
  have hq : q ≠ 0 := NeZero.ne q
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq
  rw [sum_zmod_eq_sum_range]
  have hred : ∀ n ∈ Finset.range q, reducedModulus q (n : ZMod q) = q / Nat.gcd n q := by
    intro n hn
    rw [reducedModulus, ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)]
  rw [Finset.sum_congr rfl (fun n hn => by
    rw [hred n hn, stdAddChar_neg_natCast_mul])]
  have hmaps : ∀ n ∈ Finset.range q, q / Nat.gcd n q ∈ q.divisors := by
    intro n _
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _), hq⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  -- on the fibre the weight is constant
  rw [Finset.sum_congr rfl (fun n hn => by
    rw [(Finset.mem_filter.mp hn).2])]
  rw [← Finset.sum_mul, estermannRamanujanSum]
  congr 1
  rw [sum_filter_reducedModulus_eq q hq hd]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hqed : (q : ℂ) = ((q / d : ℕ) : ℂ) * (d : ℂ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdq]
  have he0 : ((q / d : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.div_pos (Nat.le_of_dvd hq0 hdq) hd0).ne'
  have hd0C : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  congr 1
  rw [hqed]
  push_cast
  field_simp

/-- **Ramanujan sums are even.** -/
theorem estermannRamanujanSum_neg (d : ℕ) (b : ℤ) :
    estermannRamanujanSum d (-b) = estermannRamanujanSum d b := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp [estermannRamanujanSum]
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  unfold estermannRamanujanSum
  refine Finset.sum_nbij' (fun m => if m = 0 then 0 else d - m)
    (fun m => if m = 0 then 0 else d - m) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm ⊢
    by_cases h0 : m = 0
    · simp only [h0, if_true]
      exact ⟨hd0, h0 ▸ hm.2⟩
    · simp only [h0, if_false]
      refine ⟨Nat.sub_lt hd0 (Nat.pos_of_ne_zero h0), ?_⟩
      exact (Nat.coprime_self_sub_left hm.1.le).mpr hm.2
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm ⊢
    by_cases h0 : m = 0
    · simp only [h0, if_true]
      exact ⟨hd0, h0 ▸ hm.2⟩
    · simp only [h0, if_false]
      refine ⟨Nat.sub_lt hd0 (Nat.pos_of_ne_zero h0), ?_⟩
      exact (Nat.coprime_self_sub_left hm.1.le).mpr hm.2
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    by_cases h0 : m = 0
    · simp [h0]
    · have hne : d - m ≠ 0 := (Nat.sub_pos_of_lt hm.1).ne'
      simp only [h0, if_false, hne]
      exact Nat.sub_sub_self hm.1.le
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    by_cases h0 : m = 0
    · simp [h0]
    · have hne : d - m ≠ 0 := (Nat.sub_pos_of_lt hm.1).ne'
      simp only [h0, if_false, hne]
      exact Nat.sub_sub_self hm.1.le
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    by_cases h0 : m = 0
    · simp [h0]
    · simp only [h0, if_false]
      rw [Nat.cast_sub hm.1.le]
      have hper : Complex.exp (2 * π * I * (((d : ℂ) - (m : ℂ)) * (b : ℂ)) / (d : ℂ))
          = Complex.exp (2 * π * I * (-(m : ℂ) * (b : ℂ)) / (d : ℂ))
            * Complex.exp ((b : ℂ) * (2 * π * I)) := by
        rw [← Complex.exp_add]
        congr 1
        field_simp
        ring
      rw [hper, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      congr 1
      push_cast
      ring

/-- **The grouped main term.**  The progression main term is the Ramanujan expansion
`∑_{d ∣ q} c_d(b) · main(d)`. -/
theorem sum_stdAddChar_mul_main_eq_ramanujan (q : ℕ) [NeZero q] (b : ZMod q) (x : ℝ) :
    ∑ a : ZMod q, ((ZMod.stdAddChar (-(a * b))) : ℂ) *
        estermannSmoothedMain (reducedModulus q a) x
      = ∑ d ∈ q.divisors, estermannRamanujanSum d (b.val : ℤ) * estermannSmoothedMain d x := by
  rw [sum_stdAddChar_mul_reducedModulus q b (fun d => estermannSmoothedMain d x)]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [estermannRamanujanSum_neg]

/-- **The smoothed divisor sum in a progression, with its Ramanujan main term.**  For every
modulus `q`, every residue `b`, and every `x > 0`,

`‖q ∑_{N ≡ b (q)} d(N) e^{−Nx} − ∑_{d ∣ q} c_d(b) (γ − log x − 2 log d)/(dx)‖ ≤ C q^{5/2} x^{−1/2}`

with `C` absolute. -/
theorem norm_progression_sub_ramanujanMain_le (q : ℕ) [NeZero q] (b : ZMod q) {x : ℝ}
    (hx : 0 < x) :
    ‖(q : ℂ) * (∑' N : ℕ, (if (N : ZMod q) = b then ((N.divisors.card : ℂ)) else 0) *
          Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
        - ∑ d ∈ q.divisors, estermannRamanujanSum d (b.val : ℤ) * estermannSmoothedMain d x‖
      ≤ estermannSmoothedErrorConstant * (q : ℝ) ^ ((5 : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) := by
  rw [← sum_stdAddChar_mul_main_eq_ramanujan]
  exact norm_progression_sub_main_le q b hx

/-- The same expansion indexed by the complementary divisor, `∑_{d ∣ q} c_{q/d}(b) main(q/d)`,
which is the form in which the gcd reduction produces it. -/
theorem norm_progression_sub_ramanujanMain_le' (q : ℕ) [NeZero q] (b : ZMod q) {x : ℝ}
    (hx : 0 < x) :
    ‖(q : ℂ) * (∑' N : ℕ, (if (N : ZMod q) = b then ((N.divisors.card : ℂ)) else 0) *
          Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
        - ∑ d ∈ q.divisors,
            estermannRamanujanSum (q / d) (b.val : ℤ) * estermannSmoothedMain (q / d) x‖
      ≤ estermannSmoothedErrorConstant * (q : ℝ) ^ ((5 : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) := by
  rw [Nat.sum_div_divisors q
    (fun d => estermannRamanujanSum d (b.val : ℤ) * estermannSmoothedMain d x)]
  exact norm_progression_sub_ramanujanMain_le q b hx

end

end RHTower
