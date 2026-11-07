import Mathlib

/-!
# The critical coupling of the base

Why does the Gamma coupling sit at exactly the critical growth `κ = ½` of the arithmetic Bernstein theorem?

The Bernstein theorem pays a Hankel form at `y` from a torus sum at the base point `y − 2u`, with test coefficients spread over the integers or primes near `e^u`. The price is the diagonal cost
`f(y − 2u)/#(test integers near e^u)`. For the theta amplitude `f(x) = e^{x/2} Σ_{n≥1} e^{−π n² e^{2x}}`, Poisson summation says that `f` itself counts integers:

`f(x) e^{x/2} → ½` as `x → −∞` (`tendsto_thetaAmp_left`), because `Σ_n e^{−π n² e^{2x}}` counts the `n ≲ e^{−x}`.

So:

* **Integer tests balance exactly** (`tendsto_thetaAmp_integers`). `f(y − 2u) e^{−u}` tends to `e^{−y/2}/2`: a finite positive limit at every `y`. The amplitude grows at the rate at which the integers near `e^u` are counted.
* **Primes lose one logarithm** (`tendsto_thetaAmp_div_primeCounting`). With `≍ e^u/u` test primes the cost tends to `+∞`, at the rate `u`.
* **Below `½` everything is free** (`tendsto_cost_of_lt_half`). Left growth `κ < ½` has cost `e^{(2κ − 1)u} u → 0`, the hypothesis of the arithmetic Bernstein theorem.

Both `½`s are one pole. The count of integers up to `X` is `X`, the pole of `ζ` at `1`. In the theta amplitude this appears as `e^{|x|/2}`, the distance from `1` to the centre `½` of the functional equation, by Poisson. In the
diagonal cost it appears as `1/#{n ≈ e^u} = e^{−u}`: `Σ_n n^{−2σ}` diverges at `σ = ½`. The critical line is the abscissa of the diagonal, and the Gamma base is critical there because the functional equation is centred at half the pole.
-/

open Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The theta sum `Σ_{n≥1} e^{−π a n²}`. -/
def thetaSum (a : ℝ) : ℝ := ∑' n : ℕ, Real.exp (-Real.pi * a * ((n : ℝ) + 1) ^ 2)

/-- The theta amplitude `f(x) = e^{x/2} Σ_{n≥1} e^{−π n² e^{2x}}`. -/
def thetaAmp (x : ℝ) : ℝ := Real.exp (x / 2) * thetaSum (Real.exp (2 * x))

/-- A Gaussian is summable over the positive integers. -/
theorem summable_gauss {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => Real.exp (-Real.pi * a * ((n : ℝ) + 1) ^ 2) := by
  have hbase : 0 < Real.pi * a := by positivity
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun n => ?_)
    (Real.summable_exp_nat_mul_iff.mpr (show -(Real.pi * a) < 0 by linarith))
  refine Real.exp_le_exp.mpr ?_
  have h0 : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  nlinarith

/-- `Σ_{n∈ℤ} e^{−π a n²} = 1 + 2 θ(a)`. -/
theorem tsum_int_gauss {a : ℝ} (ha : 0 < a) :
    ∑' n : ℤ, Real.exp (-Real.pi * a * (n : ℝ) ^ 2) = 1 + 2 * thetaSum a := by
  have hsum := (summable_gauss ha).hasSum
  have e1 : (fun n : ℕ => Real.exp (-Real.pi * a * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2)) =
      fun n : ℕ => Real.exp (-Real.pi * a * ((n : ℝ) + 1) ^ 2) := by
    funext n
    push_cast
    rfl
  have e2 : (fun n : ℕ => Real.exp (-Real.pi * a * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) =
      fun n : ℕ => Real.exp (-Real.pi * a * ((n : ℝ) + 1) ^ 2) := by
    funext n
    push_cast
    rw [neg_sq]
  have h := HasSum.of_add_one_of_neg_add_one
    (f := fun m : ℤ => Real.exp (-Real.pi * a * (m : ℝ) ^ 2))
    (by rw [e1]; exact hsum) (by rw [e2]; exact hsum)
  rw [h.tsum_eq]
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero]
  unfold thetaSum
  ring

/-- **The functional equation of the theta sum** (Poisson summation). -/
theorem thetaSum_functional_equation {a : ℝ} (ha : 0 < a) :
    1 + 2 * thetaSum a = 1 / a ^ (1 / 2 : ℝ) * (1 + 2 * thetaSum (1 / a)) := by
  have h := Real.tsum_exp_neg_mul_int_sq ha
  rw [tsum_int_gauss ha] at h
  rw [h, ← tsum_int_gauss (a := 1 / a) (by positivity)]
  congr 2
  funext n
  congr 1
  ring

/-- The theta sum dies at infinity. -/
theorem tendsto_thetaSum_atTop : Tendsto thetaSum atTop (𝓝 0) := by
  have hb := summable_gauss (a := 1) one_pos
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℝ))
    (f := fun (b : ℝ) (k : ℕ) => Real.exp (-Real.pi * b * ((k : ℝ) + 1) ^ 2))
    (g := fun _ => (0 : ℝ))
    (bound := fun k : ℕ => Real.exp (-Real.pi * 1 * ((k : ℝ) + 1) ^ 2)) hb
    (fun k => by
      have hk : 0 < Real.pi * ((k : ℝ) + 1) ^ 2 := by positivity
      have h1 : Tendsto (fun b : ℝ => -(Real.pi * ((k : ℝ) + 1) ^ 2) * b) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      refine (Real.tendsto_exp_atBot.comp h1).congr fun b => ?_
      simp only [Function.comp]
      congr 1
      ring)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb1 k
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      refine Real.exp_le_exp.mpr ?_
      have hk : 0 ≤ Real.pi * ((k : ℝ) + 1) ^ 2 := by positivity
      nlinarith)
  simp only [tsum_zero] at hlim
  exact hlim

/-- **The amplitude counts integers.** `f(x) e^{x/2} → ½` as `x → −∞`. -/
theorem tendsto_thetaAmp_left :
    Tendsto (fun x => thetaAmp x * Real.exp (x / 2)) atBot (𝓝 (1 / 2)) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp x) atBot (𝓝 0) := Real.tendsto_exp_atBot
  have hinv : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atBot atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    exact tendsto_neg_atBot_atTop.comp (tendsto_id.const_mul_atBot (by norm_num))
  have hθ := tendsto_thetaSum_atTop.comp hinv
  have hlim : Tendsto (fun x : ℝ => (1 + 2 * (thetaSum ∘ fun x => Real.exp (-(2 * x))) x - Real.exp x) / 2)
      atBot (𝓝 ((1 + 2 * 0 - 0) / 2)) :=
    ((tendsto_const_nhds.add (hθ.const_mul 2)).sub hexp).div_const 2
  have e0 : ((1 + 2 * 0 - 0) / 2 : ℝ) = 1 / 2 := by norm_num
  rw [e0] at hlim
  refine hlim.congr fun x => ?_
  have ha : 0 < Real.exp (2 * x) := Real.exp_pos _
  have hfe := thetaSum_functional_equation ha
  have hroot : Real.exp (2 * x) ^ (1 / 2 : ℝ) = Real.exp x := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hinvexp : 1 / Real.exp (2 * x) = Real.exp (-(2 * x)) := by
    rw [Real.exp_neg, one_div]
  rw [hroot, hinvexp] at hfe
  have hmul : Real.exp x * (1 + 2 * thetaSum (Real.exp (2 * x))) = 1 + 2 * thetaSum (Real.exp (-(2 * x))) := by
    rw [hfe]
    field_simp
  simp only [Function.comp, thetaAmp]
  have hsplit : Real.exp (x / 2) * thetaSum (Real.exp (2 * x)) * Real.exp (x / 2) =
      Real.exp x * thetaSum (Real.exp (2 * x)) := by
    have : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (x / 2) * Real.exp (x / 2)) * thetaSum (Real.exp (2 * x)) := by ring
      _ = _ := by rw [this]
  rw [hsplit, ← hmul]
  ring

/-- **Integer tests balance exactly.** `f(y − 2u) e^{−u} → e^{−y/2}/2`. -/
theorem tendsto_thetaAmp_integers (y : ℝ) :
    Tendsto (fun u => thetaAmp (y - 2 * u) * Real.exp (-u)) atTop (𝓝 (Real.exp (-(y / 2)) / 2)) := by
  have hx : Tendsto (fun u : ℝ => y - 2 * u) atTop atBot :=
    tendsto_atBot_add_const_left _ y (tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))) |>.congr fun u => by
        simp only [Function.comp, id]
        ring
  have h := (tendsto_thetaAmp_left.comp hx).mul_const (Real.exp (-(y / 2)))
  have e0 : (1 / 2 : ℝ) * Real.exp (-(y / 2)) = Real.exp (-(y / 2)) / 2 := by ring
  rw [e0] at h
  refine h.congr fun u => ?_
  simp only [Function.comp]
  have e : Real.exp ((y - 2 * u) / 2) * Real.exp (-(y / 2)) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc, e]

/-- **Primes lose one logarithm.** Against the primes up to `e^{u+1}` the diagonal cost of the theta amplitude tends to `+∞`. -/
theorem tendsto_thetaAmp_div_primeCounting (y : ℝ) :
    Tendsto (fun u => thetaAmp (y - 2 * u) / Nat.primeCounting ⌊Real.exp (u + 1)⌋₊) atTop atTop := by
  have hc : 0 < Real.exp (-(y / 2)) / 2 := by positivity
  have hlog4 : 0 < Real.log 4 + 1 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  set K : ℝ := (Real.log 4 + 1) * Real.exp 1 with hK
  have hK0 : 0 < K := by positivity
  have h1 := tendsto_thetaAmp_integers y
  have h2 : Tendsto (fun u : ℝ => (u + 1) / K) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ tendsto_id).atTop_div_const hK0
  have hprod := h1.pos_mul_atTop hc h2
  refine tendsto_atTop_mono' _ ?_ hprod
  have hexpTend : Tendsto (fun u : ℝ => Real.exp (u + 1)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have hcheb := hexpTend.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  have hpos2 := hexpTend.eventually_ge_atTop 2
  have hthetapos : ∀ᶠ u : ℝ in atTop, 0 ≤ thetaAmp (y - 2 * u) := by
    refine Eventually.of_forall fun u => ?_
    unfold thetaAmp thetaSum
    exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)
  filter_upwards [hcheb, hpos2, hthetapos, eventually_gt_atTop (0 : ℝ)] with u hu hu2 hth hu0
  rw [Real.log_exp] at hu
  have hpi : (1 : ℝ) ≤ Nat.primeCounting ⌊Real.exp (u + 1)⌋₊ := by
    have h3 : 2 ≤ ⌊Real.exp (u + 1)⌋₊ := Nat.le_floor (by exact_mod_cast hu2)
    have h4 := Nat.monotone_primeCounting h3
    have h5 : Nat.primeCounting 2 = 1 := by decide
    exact_mod_cast h5 ▸ h4
  have hpi0 : (0 : ℝ) < Nat.primeCounting ⌊Real.exp (u + 1)⌋₊ := by linarith
  rw [le_div_iff₀ hpi0]
  have hbound : (Nat.primeCounting ⌊Real.exp (u + 1)⌋₊ : ℝ) ≤ K * Real.exp u / (u + 1) := by
    refine hu.trans (le_of_eq ?_)
    rw [hK, Real.exp_add]
    ring
  have hu1 : 0 < u + 1 := by linarith
  calc
    thetaAmp (y - 2 * u) * Real.exp (-u) * ((u + 1) / K) * (Nat.primeCounting ⌊Real.exp (u + 1)⌋₊ : ℝ)
        ≤ thetaAmp (y - 2 * u) * Real.exp (-u) * ((u + 1) / K) * (K * Real.exp u / (u + 1)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = thetaAmp (y - 2 * u) := by
        have he : Real.exp (-u) * Real.exp u = 1 := by
          rw [← Real.exp_add]
          simp
        field_simp
        rw [mul_assoc, he, mul_one]

/-- **Below `½` the diagonal is free.** For `κ < ½` the cost `e^{2κu} (u + 1) e^{−u}` tends to `0`. -/
theorem tendsto_cost_of_lt_half {κ : ℝ} (hκ : κ < 1 / 2) :
    Tendsto (fun u : ℝ => Real.exp (2 * κ * u) * (u + 1) * Real.exp (-u)) atTop (𝓝 0) := by
  have hb : 0 < 1 - 2 * κ := by linarith
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 - 2 * κ) hb
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 - 2 * κ) hb
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [Real.rpow_one, Real.rpow_zero]
  have e : Real.exp (2 * κ * u) * (u + 1) * Real.exp (-u) =
      (u + 1) * (Real.exp (2 * κ * u) * Real.exp (-u)) := by ring
  rw [e, ← Real.exp_add]
  have e2 : 2 * κ * u + -u = -(1 - 2 * κ) * u := by ring
  rw [e2]
  ring

end

end GaloisForLFunctions.PrimeTorusTheory
