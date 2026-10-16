import GaloisForLFunctions.RHTower.RiemannKernelTransformInjectivity
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct

/-!
# Divisor coordinates for the complete prime Doob energy

Reflection of the Riemann kernel and logarithmic translation turn the two theta indices and
the prime-power index into a chain of divisors. The analytic estimates below justify retaining
all three indices in this change of coordinates.
-/

open MeasureTheory Polynomial

namespace RHTower.PhiDivisorEnergy

noncomputable section

/-- The common theta weight at product index `N`, in logarithmic coordinates. -/
def fiber (N : ℕ) (u : ℝ) : ℝ :=
  cuspTerm riemannCuspPoly 1 u * cuspTerm riemannCuspPoly N (-u)

/-- The von Mangoldt graph energy on the divisors of `N`. -/
def divisorEnergy (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ k ∈ N.divisors, ∑ m ∈ k.divisors,
    ArithmeticFunction.vonMangoldt (k / m) * (a m - a k) ^ 2

private def envelope (u : ℝ) : ℝ :=
  (2 + Real.exp (2 * u) + Real.exp (-2 * u)) *
    Real.exp (-Real.pi * Real.cosh (2 * u))

private def polyBound : ℝ := 4 * Real.pi ^ 2 + 6 * Real.pi

private theorem cuspPoly_eval (t : ℝ) :
    riemannCuspPoly.eval t = 4 * Real.pi ^ 2 * t ^ 2 - 6 * Real.pi * t := by
  simp [riemannCuspPoly, cuspDeriv]
  ring

private theorem abs_cuspPoly_eval_le {t : ℝ} (ht : 0 ≤ t) :
    |riemannCuspPoly.eval t| ≤ polyBound * (t ^ 2 + t) := by
  rw [cuspPoly_eval]
  calc
    _ ≤ |4 * Real.pi ^ 2 * t ^ 2| + |6 * Real.pi * t| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (4 * Real.pi ^ 2 * t ^ 2) (6 * Real.pi * t)
    _ = 4 * Real.pi ^ 2 * t ^ 2 + 6 * Real.pi * t := by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ _ := by
      dsimp [polyBound]
      nlinarith [mul_nonneg (show 0 ≤ 4 * Real.pi ^ 2 by positivity) ht,
        mul_nonneg (show 0 ≤ 6 * Real.pi by positivity) (sq_nonneg t)]

private theorem fiber_explicit (N : ℕ) (u : ℝ) :
    fiber N u = riemannCuspPoly.eval (Real.exp (2 * u)) *
      riemannCuspPoly.eval ((N : ℝ) ^ 2 * Real.exp (-2 * u)) *
        Real.exp (-Real.pi * (Real.exp (2 * u) + (N : ℝ) ^ 2 * Real.exp (-2 * u))) := by
  unfold fiber cuspTerm
  simp only [Nat.cast_one, one_pow, one_mul]
  rw [show 2 * -u = -2 * u by ring]
  have he : Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show u / 2 + -u / 2 = 0 by ring, Real.exp_zero]
  rw [mul_add, Real.exp_add]
  calc
    _ = (Real.exp (u / 2) * Real.exp (-u / 2)) *
        (riemannCuspPoly.eval (Real.exp (2 * u)) *
          riemannCuspPoly.eval ((N : ℝ) ^ 2 * Real.exp (-2 * u)) *
            (Real.exp (-Real.pi * Real.exp (2 * u)) *
              Real.exp (-Real.pi * ((N : ℝ) ^ 2 * Real.exp (-2 * u))))) := by ring
    _ = _ := by rw [he, one_mul]

private theorem envelope_nonneg (u : ℝ) : 0 ≤ envelope u := by
  unfold envelope
  positivity

private theorem integrable_real_exp_cosh (h : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-Real.pi * Real.cosh (2 * u) + h * (2 * u))) := by
  have heq (t : ℝ) :
      (GaloisForLFunctions.RHTower.besselOrderExpKernel Real.pi (h : ℂ) t).re =
        Real.exp (-Real.pi * Real.cosh t + h * t) := by
    have ha : -(Real.pi : ℂ) * Complex.cosh (t : ℂ) + (h : ℂ) * (t : ℂ) =
        ((-Real.pi * Real.cosh t + h * t : ℝ) : ℂ) := by
      simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_cosh]
    rw [GaloisForLFunctions.RHTower.besselOrderExpKernel, ha, Complex.exp_ofReal_re]
  have hi' : Integrable (fun t : ℝ => Real.exp (-Real.pi * Real.cosh t + h * t)) := by
    simpa only [RCLike.re_eq_complex_re, heq] using
      (GaloisForLFunctions.RHTower.integrable_besselOrderExpKernel Real.pi_pos (h : ℂ)).re
  exact hi'.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)

private theorem integrable_envelope : Integrable envelope := by
  have h0 := (integrable_real_exp_cosh 0).const_mul 2
  have h1 := integrable_real_exp_cosh 1
  have hm := integrable_real_exp_cosh (-1)
  refine ((h0.add h1).add hm).congr (ae_of_all _ fun u => ?_)
  simp only [Pi.add_apply, envelope, zero_mul, add_zero, one_mul, neg_one_mul, Real.exp_add]
  rw [show -(2 * u) = -2 * u by ring]
  ring

private theorem fiber_bound {N : ℕ} (hN : 0 < N) (u : ℝ) :
    ‖fiber N u‖ ≤ polyBound ^ 2 * (N : ℝ) ^ 4 * Real.exp (-Real.pi * N) * envelope u := by
  let A := Real.exp (2 * u)
  let B := (N : ℝ) ^ 2 * Real.exp (-2 * u)
  let C := Real.exp (-2 * u)
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) hC
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hAC : A * C = 1 := by
    dsimp [A, C]
    rw [← Real.exp_add, show 2 * u + -2 * u = 0 by ring, Real.exp_zero]
  have hAB : A * B = (N : ℝ) ^ 2 := by
    dsimp only [B]
    calc
      _ = (N : ℝ) ^ 2 * (A * C) := by dsimp [C]; ring
      _ = _ := by rw [hAC, mul_one]
  have hpoly : (A ^ 2 + A) * (B ^ 2 + B) ≤ (N : ℝ) ^ 4 * (2 + A + C) := by
    calc
      _ = (A * B) * (A * B + A + B + 1) := by ring
      _ = (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + A + (N : ℝ) ^ 2 * C + 1) := by
        rw [hAB]
      _ ≤ _ := by
        have hh := mul_nonneg (sq_nonneg (N : ℝ))
          (mul_nonneg (sub_nonneg.mpr hN2) (show 0 ≤ A + 1 by positivity))
        nlinarith only [hh]
  have hexpProd : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hexpSq : Real.exp u ^ 2 = A := by
    rw [pow_two, ← Real.exp_add, show u + u = 2 * u by ring]
  have hexpNegSq : Real.exp (-u) ^ 2 = C := by
    rw [pow_two, ← Real.exp_add, show -u + -u = -2 * u by ring]
  have hgauss : (N : ℝ) + Real.cosh (2 * u) ≤ A + B := by
    have hsq := sq_nonneg (Real.exp u - (N : ℝ) * Real.exp (-u))
    have hsq' : 2 * (N : ℝ) ≤ A + B := by
      nlinarith [hexpSq, hexpNegSq, hexpProd]
    have hBC : C ≤ B := by
      exact le_mul_of_one_le_left hC hN2
    have hcosh : Real.cosh (2 * u) = (A + C) / 2 := by
      rw [Real.cosh_eq, show -(2 * u) = -2 * u by ring]
    rw [hcosh]
    linarith
  have he : Real.exp (-Real.pi * (A + B)) ≤
      Real.exp (-Real.pi * N) * Real.exp (-Real.pi * Real.cosh (2 * u)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hgauss Real.pi_pos.le]
  have hp : 0 ≤ polyBound := by unfold polyBound; positivity
  rw [fiber_explicit, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  change |riemannCuspPoly.eval A| * |riemannCuspPoly.eval B| *
    Real.exp (-Real.pi * (A + B)) ≤ _
  calc
    _ ≤ (polyBound * (A ^ 2 + A)) * (polyBound * (B ^ 2 + B)) *
        Real.exp (-Real.pi * (A + B)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (abs_cuspPoly_eval_le hA) (abs_cuspPoly_eval_le hB)
          (abs_nonneg _) (mul_nonneg hp (by positivity))) (Real.exp_pos _).le
    _ = polyBound ^ 2 * ((A ^ 2 + A) * (B ^ 2 + B)) *
        Real.exp (-Real.pi * (A + B)) := by ring
    _ ≤ (polyBound ^ 2 * ((N : ℝ) ^ 4 * (2 + A + C))) *
        (Real.exp (-Real.pi * N) * Real.exp (-Real.pi * Real.cosh (2 * u))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpoly (sq_nonneg _)) he
        (Real.exp_pos _).le (by positivity)
    _ = _ := by dsimp [envelope, A, C]; ring

private theorem continuous_fiber (N : ℕ) : Continuous (fiber N) := by
  unfold fiber cuspTerm
  fun_prop

private theorem integrable_fiber {N : ℕ} (hN : 0 < N) : Integrable (fiber N) :=
  (integrable_envelope.const_mul _).mono' (continuous_fiber N).aestronglyMeasurable
    (ae_of_all _ (fiber_bound hN))

/-- One divisor edge, with both theta indices retained in the product index. -/
def edge (v : ℝ → ℝ) (m d n : ℕ) (u : ℝ) : ℝ :=
  ArithmeticFunction.vonMangoldt d * fiber (m * d * n) u *
    (v (u - Real.log m) - v (u - Real.log ((m * d : ℕ) : ℝ))) ^ 2

private theorem cusp_pair_to_fiber {m d n : ℕ} (hm : 0 < m) (hd : 0 < d) (x : ℝ) :
    cuspTerm riemannCuspPoly m x * cuspTerm riemannCuspPoly n (Real.log d - x) =
      Real.sqrt d * fiber (m * d * n) (x + Real.log m) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hlog : Real.log (m * d : ℕ) = Real.log m + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hm0 hd0]
  have harg : -(x + Real.log m) + Real.log (m * d : ℕ) = Real.log d - x := by
    rw [hlog]
    ring
  have hn := cuspTerm_add_log riemannCuspPoly n (Nat.mul_pos hm hd) (-(x + Real.log m))
  rw [harg, Nat.cast_mul, Real.sqrt_mul (by positivity)] at hn
  rw [fiber, cuspTerm_add_log riemannCuspPoly 1 hm, Nat.mul_one, hn]
  ring

private theorem continuous_edge {v : ℝ → ℝ} (hv : Continuous v) (m d n : ℕ) :
    Continuous (edge v m d n) := by
  unfold edge
  have h : Continuous (fun u => v (u - Real.log m) -
      v (u - Real.log ((m * d : ℕ) : ℝ))) := by fun_prop
  exact (continuous_const.mul (continuous_fiber _)).mul (h.pow 2)

private theorem difference_sq_le {v : ℝ → ℝ} {M : ℝ} (_hM : 0 ≤ M)
    (hv : ∀ u, |v u| ≤ M) (x y : ℝ) : (v x - v y) ^ 2 ≤ 4 * M ^ 2 := by
  have hx := abs_le.mp (hv x)
  have hy := abs_le.mp (hv y)
  have h := mul_nonneg (show 0 ≤ 2 * M - (v x - v y) by linarith)
    (show 0 ≤ 2 * M + (v x - v y) by linarith)
  nlinarith only [h]

private def seqBound (n : ℕ+) : ℝ :=
  ((n : ℕ) : ℝ) ^ 5 * Real.exp (-(Real.pi / 3) * (n : ℕ))

private theorem seqBound_nonneg (n : ℕ+) : 0 ≤ seqBound n := by
  unfold seqBound
  positivity

private theorem summable_seqBound : Summable seqBound := by
  apply Equiv.pnatEquivNat.symm.summable_iff.mp
  change Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 5 *
    Real.exp (-(Real.pi / 3) * (n + 1 : ℕ)))
  exact summable_cuspTerm_bound 5 (show 0 < Real.pi / 3 by positivity)

private theorem product_decay_le (m d n : ℕ+) :
    (((m : ℕ) : ℝ) * (d : ℕ) * (n : ℕ)) ^ 5 *
      Real.exp (-Real.pi * (((m : ℕ) : ℝ) * (d : ℕ) * (n : ℕ))) ≤
        seqBound m * seqBound d * seqBound n := by
  have hm : (1 : ℝ) ≤ (m : ℕ) := by exact_mod_cast m.pos
  have hd : (1 : ℝ) ≤ (d : ℕ) := by exact_mod_cast d.pos
  have hn : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.pos
  have hmd : (1 : ℝ) ≤ (m : ℕ) * (d : ℕ) := by nlinarith
  have hmn : (1 : ℝ) ≤ (m : ℕ) * (n : ℕ) := by nlinarith
  have hdn : (1 : ℝ) ≤ (d : ℕ) * (n : ℕ) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hdn (show (0 : ℝ) ≤ (m : ℕ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hmn (show (0 : ℝ) ≤ (d : ℕ) by positivity)
  have h3 := mul_le_mul_of_nonneg_right hmd (show (0 : ℝ) ≤ (n : ℕ) by positivity)
  have hs : ((m : ℕ) : ℝ) + (d : ℕ) + (n : ℕ) ≤
      3 * (((m : ℕ) : ℝ) * (d : ℕ) * (n : ℕ)) := by nlinarith only [h1, h2, h3]
  have he : Real.exp (-Real.pi * (((m : ℕ) : ℝ) * (d : ℕ) * (n : ℕ))) ≤
      Real.exp (-(Real.pi / 3) * (m : ℕ)) * Real.exp (-(Real.pi / 3) * (d : ℕ)) *
        Real.exp (-(Real.pi / 3) * (n : ℕ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_pos.le]
  calc
    _ ≤ ((((m : ℕ) : ℝ) * (d : ℕ) * (n : ℕ)) ^ 5) *
        (Real.exp (-(Real.pi / 3) * (m : ℕ)) * Real.exp (-(Real.pi / 3) * (d : ℕ)) *
          Real.exp (-(Real.pi / 3) * (n : ℕ))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by simp only [seqBound, mul_pow]; ring

private theorem edge_bound {v : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ u, |v u| ≤ M) (m d n : ℕ+) (u : ℝ) :
    ‖edge v m d n u‖ ≤
      (4 * M ^ 2 * polyBound ^ 2 * (seqBound m * seqBound d * seqBound n)) * envelope u := by
  let N : ℕ := m * d * n
  have hN : 0 < N := Nat.mul_pos (Nat.mul_pos m.pos d.pos) n.pos
  have hdN : d ≤ N := by
    dsimp [N]
    calc
      (d : ℕ) = 1 * (d : ℕ) * 1 := by simp
      _ ≤ (m : ℕ) * (d : ℕ) * (n : ℕ) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ m.pos) n.pos
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt (d : ℕ) := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ : ArithmeticFunction.vonMangoldt (d : ℕ) ≤ (N : ℝ) := by
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (d : ℕ) by positivity)
    have hdN' : ((d : ℕ) : ℝ) ≤ N := by exact_mod_cast hdN
    linarith [ArithmeticFunction.vonMangoldt_le_log (n := (d : ℕ))]
  have hdif := difference_sq_le hM hv (u - Real.log (m : ℕ))
    (u - Real.log (((m : ℕ) * (d : ℕ) : ℕ) : ℝ))
  have hpoly := fiber_bound hN u
  have henv := envelope_nonneg u
  have hdec : (N : ℝ) ^ 5 * Real.exp (-Real.pi * N) ≤
      seqBound m * seqBound d * seqBound n := by
    simpa only [N, Nat.cast_mul] using product_decay_le m d n
  rw [edge, norm_mul, norm_mul, Real.norm_of_nonneg hΛ0,
    Real.norm_of_nonneg (sq_nonneg (v (u - Real.log (m : ℕ)) -
      v (u - Real.log (((m : ℕ) * (d : ℕ) : ℕ) : ℝ))))]
  calc
    _ ≤ ((N : ℝ) * (polyBound ^ 2 * (N : ℝ) ^ 4 * Real.exp (-Real.pi * N) * envelope u)) *
        (4 * M ^ 2) :=
      mul_le_mul (mul_le_mul hΛ hpoly (norm_nonneg _) (by positivity)) hdif
        (sq_nonneg _) (by positivity)
    _ = (4 * M ^ 2 * polyBound ^ 2 * ((N : ℝ) ^ 5 * Real.exp (-Real.pi * N))) *
        envelope u := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdec (by positivity)) (envelope_nonneg u)

/-- Each complete theta-divisor edge is integrable for bounded continuous input. -/
theorem integrable_edge {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) (m d n : ℕ+) : Integrable (edge v m d n) :=
  (integrable_envelope.const_mul _).mono' (continuous_edge hv m d n).aestronglyMeasurable
    (ae_of_all _ (edge_bound hM hvM m d n))

/-- Absolute convergence over both theta indices and the complete prime-power index. -/
theorem summable_integral_norm_edge {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    Summable (fun p : (ℕ+ × ℕ+) × ℕ+ => ∫ u, ‖edge v p.1.1 p.1.2 p.2 u‖) := by
  have hs2 := summable_seqBound.mul_of_nonneg summable_seqBound seqBound_nonneg seqBound_nonneg
  have hs := hs2.mul_of_nonneg summable_seqBound (fun p => mul_nonneg (seqBound_nonneg p.1)
      (seqBound_nonneg p.2)) seqBound_nonneg
  have hs' := (hs.mul_left (4 * M ^ 2 * polyBound ^ 2)).mul_right (∫ u, envelope u)
  apply hs'.of_nonneg_of_le (fun p => integral_nonneg fun u => norm_nonneg _) (fun p => ?_)
  rw [← integral_const_mul]
  exact integral_mono (integrable_edge hv hM hvM p.1.1 p.1.2 p.2).norm
    (integrable_envelope.const_mul _) (edge_bound hM hvM p.1.1 p.1.2 p.2)

private abbrev Chains (N : ℕ+) :=
  Σ c : (N : ℕ).divisorsAntidiagonal, c.val.1.divisorsAntidiagonal

private def chainEquiv : (Σ N : ℕ+, Chains N) ≃ (ℕ+ × ℕ+) × ℕ+ where
  toFun z :=
    ((⟨z.2.2.val.1, Nat.pos_of_mem_divisors
        (Nat.fst_mem_divisors_of_mem_antidiagonal z.2.2.property)⟩,
      ⟨z.2.2.val.2, Nat.pos_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal z.2.2.property)⟩),
      ⟨z.2.1.val.2, Nat.pos_of_mem_divisors
        (Nat.snd_mem_divisors_of_mem_antidiagonal z.2.1.property)⟩)
  invFun p :=
    ⟨⟨(p.1.1 : ℕ) * (p.1.2 : ℕ) * (p.2 : ℕ),
        Nat.mul_pos (Nat.mul_pos p.1.1.pos p.1.2.pos) p.2.pos⟩,
      ⟨⟨((p.1.1 : ℕ) * (p.1.2 : ℕ), (p.2 : ℕ)),
          Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, by positivity⟩⟩,
        ⟨((p.1.1 : ℕ), (p.1.2 : ℕ)),
          Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, by positivity⟩⟩⟩⟩
  left_inv := by
    rintro ⟨⟨N, hN⟩, ⟨⟨⟨k, n⟩, hkn⟩, ⟨⟨m, d⟩, hmd⟩⟩⟩
    have h1 := (Nat.mem_divisorsAntidiagonal.mp hkn).1
    have h2 := (Nat.mem_divisorsAntidiagonal.mp hmd).1
    change k * n = N at h1
    change m * d = k at h2
    subst k
    subst N
    rfl
  right_inv := fun _ => rfl

/-- Absolute triple sums regroup by their product into finite divisor chains. -/
theorem hasSum_chains {F : ℕ → ℕ → ℕ → ℝ}
    (hF : Summable (fun p : (ℕ+ × ℕ+) × ℕ+ => F p.1.1 p.1.2 p.2)) :
    HasSum (fun N : ℕ+ => ∑ c ∈ (N : ℕ).divisorsAntidiagonal,
      ∑ q ∈ c.1.divisorsAntidiagonal, F q.1 q.2 c.2)
      (∑' p : (ℕ+ × ℕ+) × ℕ+, F p.1.1 p.1.2 p.2) := by
  let f : (ℕ+ × ℕ+) × ℕ+ → ℝ := fun p => F p.1.1 p.1.2 p.2
  have hh := (chainEquiv.hasSum_iff (f := f)).mpr hF.hasSum
  apply hh.sigma
  intro N
  have hsum :
      (∑ c ∈ (N : ℕ).divisorsAntidiagonal.attach,
        ∑ q ∈ c.val.1.divisorsAntidiagonal.attach, F q.val.1 q.val.2 c.val.2) =
      ∑ c ∈ (N : ℕ).divisorsAntidiagonal, ∑ q ∈ c.1.divisorsAntidiagonal, F q.1 q.2 c.2 := by
    calc
      _ = ∑ c ∈ (N : ℕ).divisorsAntidiagonal.attach,
          ∑ q ∈ c.val.1.divisorsAntidiagonal, F q.1 q.2 c.val.2 := by
        apply Finset.sum_congr rfl
        intro c _
        exact c.val.1.divisorsAntidiagonal.sum_attach (fun q => F q.1 q.2 c.val.2)
      _ = _ := (N : ℕ).divisorsAntidiagonal.sum_attach
        (fun c => ∑ q ∈ c.1.divisorsAntidiagonal, F q.1 q.2 c.2)
  have hfin := hasSum_fintype (fun c : Chains N => f (chainEquiv ⟨N, c⟩))
  simp only [Chains, f, chainEquiv, Equiv.coe_fn_mk, PNat.mk_coe,
    Fintype.sum_sigma, Finset.univ_eq_attach] at hfin
  rw [hsum] at hfin
  exact hfin

private theorem divisor_integrand_eq (v : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    fiber N u * divisorEnergy N (fun m => v (u - Real.log m)) =
      ∑ c ∈ N.divisorsAntidiagonal, ∑ q ∈ c.1.divisorsAntidiagonal,
        edge v q.1 q.2 c.2 u := by
  rw [Nat.sum_divisorsAntidiagonal (fun k n =>
    ∑ q ∈ k.divisorsAntidiagonal, edge v q.1 q.2 n u)]
  unfold divisorEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.sum_divisorsAntidiagonal (fun m d => edge v m d (N / k) u), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [edge, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hm),
    Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hk)]
  ring

private theorem integral_divisor_eq {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) (N : ℕ) :
    (∫ u, fiber N u * divisorEnergy N (fun m => v (u - Real.log m))) =
      ∑ c ∈ N.divisorsAntidiagonal, ∑ q ∈ c.1.divisorsAntidiagonal,
        ∫ u, edge v q.1 q.2 c.2 u := by
  have hi (c : ℕ × ℕ) (hc : c ∈ N.divisorsAntidiagonal)
      (q : ℕ × ℕ) (hq : q ∈ c.1.divisorsAntidiagonal) : Integrable (edge v q.1 q.2 c.2) :=
    integrable_edge hv hM hvM
      ⟨q.1, Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hq)⟩
      ⟨q.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hq)⟩
      ⟨c.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hc)⟩
  simp_rw [divisor_integrand_eq]
  rw [integral_finsetSum _ (fun c hc => integrable_finsetSum _ (hi c hc))]
  apply Finset.sum_congr rfl
  intro c hc
  exact integral_finsetSum _ (hi c hc)

private theorem shifted_edge_eq (v : ℝ → ℝ) {m d n : ℕ}
    (hm : 0 < m) (hd : 0 < d) (x : ℝ) :
    edge v m d n (x + Real.log m) =
      ((ArithmeticFunction.vonMangoldt d / Real.sqrt d) *
        (v x - v (x - Real.log d)) ^ 2) *
          (cuspTerm riemannCuspPoly m x * cuspTerm riemannCuspPoly n (Real.log d - x)) := by
  have hlog : Real.log (m * d : ℕ) = Real.log m + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [edge, show x + Real.log m - Real.log m = x by ring, hlog,
    show x + Real.log m - (Real.log m + Real.log d) = x - Real.log d by ring,
    cusp_pair_to_fiber hm hd]
  field_simp

private theorem summable_cusp_pnat (R : ℝ[X]) (x : ℝ) :
    Summable (fun m : ℕ+ => cuspTerm R m x) := by
  apply Equiv.pnatEquivNat.symm.summable_iff.mp
  change Summable (fun m : ℕ => cuspTerm R (m + 1) x)
  exact summable_cuspTerm R x

private theorem tsum_cusp_pnat (R : ℝ[X]) (x : ℝ) :
    (∑' m : ℕ+, cuspTerm R m x) = cuspSeries R x := by
  have hh := Equiv.pnatEquivNat.symm.tsum_eq (fun m : ℕ+ => cuspTerm R m x)
  exact hh.symm

/-- Summing both theta indices recovers the actual prime jump at every point. -/
theorem tsum_shifted_edge_eq (v : ℝ → ℝ) (d : ℕ+) (x : ℝ) :
    (∑' p : ℕ+ × ℕ+, edge v p.1 d p.2 (x + Real.log (p.1 : ℕ))) =
      phiDoobPrimeJump v d (x - Real.log (d : ℕ)) := by
  have h1 := summable_cusp_pnat riemannCuspPoly x
  have h2 := summable_cusp_pnat riemannCuspPoly (Real.log (d : ℕ) - x)
  have hp := summable_mul_of_summable_norm h1.norm h2.norm
  simp_rw [shifted_edge_eq v (PNat.pos _) d.pos]
  rw [tsum_mul_left, ← h1.tsum_mul_tsum h2 hp, tsum_cusp_pnat, tsum_cusp_pnat,
    cuspSeries_riemannCuspPoly_eq, cuspSeries_riemannCuspPoly_eq]
  have hrefl : riemannKernelReal (x - Real.log (d : ℕ)) =
      riemannKernelReal (Real.log (d : ℕ) - x) := by
    simp only [riemannKernelReal, abs_sub_comm]
  rw [phiDoobPrimeJump, show x - Real.log (d : ℕ) + Real.log (d : ℕ) = x by ring, hrefl]
  by_cases hd : 2 ≤ (d : ℕ)
  · rw [vonMangoldtAtom, if_pos hd]
    ring
  · have hd1 : (d : ℕ) = 1 := by have := d.pos; omega
    simp only [hd1, ArithmeticFunction.vonMangoldt_apply_one, vonMangoldtAtom]
    norm_num

/-- Reordering the complete edge indices with the prime-power index first. -/
def primeFirstEquiv : (ℕ+ × (ℕ+ × ℕ+)) ≃ ((ℕ+ × ℕ+) × ℕ+) where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private theorem integral_prime_eq {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) (d : ℕ+) :
    (∫ u, phiDoobPrimeJump v d u) =
      ∑' p : ℕ+ × ℕ+, ∫ u, edge v p.1 d p.2 u := by
  have hs := (primeFirstEquiv.summable_iff).mpr (summable_integral_norm_edge hv hM hvM)
  change Summable (fun q : ℕ+ × (ℕ+ × ℕ+) => ∫ u, ‖edge v q.2.1 q.1 q.2.2 u‖) at hs
  have hd : Summable (fun p : ℕ+ × ℕ+ =>
      ∫ x, ‖edge v p.1 d p.2 (x + Real.log (p.1 : ℕ))‖) := by
    exact (hs.prod_factor d).congr (fun p =>
      (integral_add_right_eq_self (fun u => ‖edge v p.1 d p.2 u‖)
        (Real.log (p.1 : ℕ))).symm)
  have hi := integral_tsum_of_summable_integral_norm
    (fun p : ℕ+ × ℕ+ => (integrable_edge hv hM hvM p.1 d p.2).comp_add_right
      (Real.log (p.1 : ℕ))) hd
  simp_rw [tsum_shifted_edge_eq, integral_add_right_eq_self] at hi
  simpa only [sub_eq_add_neg, integral_add_right_eq_self] using hi.symm

/-- The complete original prime-jump series converges for every bounded continuous test. -/
theorem summable_integral_primeJump {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    Summable (fun d : ℕ+ => ∫ u, phiDoobPrimeJump v d u) := by
  have hs : Summable (fun p : (ℕ+ × ℕ+) × ℕ+ => ∫ u, edge v p.1.1 p.1.2 p.2 u) :=
    (summable_integral_norm_edge hv hM hvM).of_norm_bounded
      (fun p => norm_integral_le_integral_norm _)
  have hp := primeFirstEquiv.summable_iff.mpr hs
  change Summable (fun q : ℕ+ × (ℕ+ × ℕ+) => ∫ u, edge v q.2.1 q.1 q.2.2 u) at hp
  simpa only [integral_prime_eq hv hM hvM] using hp.prod

/-- The complete prime Doob energy is an absolutely convergent sum of divisor-graph energies.
Every pair of theta indices and every prime power occur in this identity. -/
theorem primeEnergy_divisor_hasSum {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    HasSum (fun N : ℕ+ => ∫ u, fiber N u * divisorEnergy N (fun m => v (u - Real.log m)))
      (∑' d : ℕ+, ∫ u, phiDoobPrimeJump v d u) := by
  have hs : Summable (fun p : (ℕ+ × ℕ+) × ℕ+ => ∫ u, edge v p.1.1 p.1.2 p.2 u) :=
    (summable_integral_norm_edge hv hM hvM).of_norm_bounded
      (fun p => norm_integral_le_integral_norm _)
  have hp := primeFirstEquiv.summable_iff.mpr hs
  change Summable (fun q : ℕ+ × (ℕ+ × ℕ+) => ∫ u, edge v q.2.1 q.1 q.2.2 u) at hp
  have ht : (∑' d : ℕ+, ∫ u, phiDoobPrimeJump v d u) =
      ∑' p : (ℕ+ × ℕ+) × ℕ+, ∫ u, edge v p.1.1 p.1.2 p.2 u := by
    simp_rw [integral_prime_eq hv hM hvM]
    rw [← hp.tsum_prod]
    exact primeFirstEquiv.tsum_eq
      (fun p : (ℕ+ × ℕ+) × ℕ+ => ∫ u, edge v p.1.1 p.1.2 p.2 u)
  rw [ht]
  simpa only [integral_divisor_eq hv hM hvM] using
    hasSum_chains (F := fun m d n => ∫ u, edge v m d n u) hs

/-- Exact quadratic divisor decomposition of the full prime term. -/
theorem primeEnergy_eq_tsum_divisorEnergy {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    (∑' d : ℕ+, ∫ u, phiDoobPrimeJump v d u) =
      ∑' N : ℕ+, ∫ u, fiber N u * divisorEnergy N (fun m => v (u - Real.log m)) :=
  (primeEnergy_divisor_hasSum hv hM hvM).tsum_eq.symm

/-- The full quadratic identity on the compactly supported test class. -/
theorem primeEnergy_eq_tsum_divisorEnergy_compact {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    (∑' d : ℕ+, ∫ u, phiDoobPrimeJump v d u) =
      ∑' N : ℕ+, ∫ u, fiber N u * divisorEnergy N (fun m => v (u - Real.log m)) := by
  obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv
  exact primeEnergy_eq_tsum_divisorEnergy hv ((norm_nonneg (v 0)).trans (hM 0))
    (fun u => by simpa only [Real.norm_eq_abs] using hM u)

private theorem primeEnergy_nat_eq_pnat {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    (∑' d : ℕ, ∫ u, phiDoobPrimeJump v d u) = ∑' d : ℕ+, ∫ u, phiDoobPrimeJump v d u := by
  have hs := Equiv.pnatEquivNat.symm.summable_iff.mpr (summable_integral_primeJump hv hM hvM)
  change Summable (fun d : ℕ => ∫ u, phiDoobPrimeJump v (d + 1) u) at hs
  have hz : (∫ u, phiDoobPrimeJump v 0 u) = 0 := by
    simp only [phiDoobPrimeJump, vonMangoldtAtom, show ¬2 ≤ (0 : ℕ) by omega, if_false,
      zero_mul, integral_zero]
  rw [tsum_eq_zero_add' hs, hz, zero_add]
  exact Equiv.pnatEquivNat.symm.tsum_eq (fun d : ℕ+ => ∫ u, phiDoobPrimeJump v d u)

/-- The divisor decomposition with exactly the natural-number prime sum used by the Doob form. -/
theorem primeEnergy_nat_eq_tsum_divisorEnergy {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    (∑' d : ℕ, ∫ u, phiDoobPrimeJump v d u) =
      ∑' N : ℕ+, ∫ u, fiber N u * divisorEnergy N (fun m => v (u - Real.log m)) :=
  (primeEnergy_nat_eq_pnat hv hM hvM).trans (primeEnergy_eq_tsum_divisorEnergy hv hM hvM)

/-- The exact prime term in the HF Dirichlet criterion, expressed on divisor graphs. -/
theorem primeEnergy_nat_eq_tsum_divisorEnergy_compact {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    (∑' d : ℕ, ∫ u, phiDoobPrimeJump v d u) =
      ∑' N : ℕ+, ∫ u, fiber N u * divisorEnergy N (fun m => v (u - Real.log m)) := by
  obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv
  exact primeEnergy_nat_eq_tsum_divisorEnergy hv ((norm_nonneg (v 0)).trans (hM 0))
    (fun u => by simpa only [Real.norm_eq_abs] using hM u)

/-- Positivity of the complete signed divisor average follows from the original prime jumps. -/
theorem tsum_divisorEnergy_nonneg {v : ℝ → ℝ} (hv : Continuous v) {M : ℝ}
    (hM : 0 ≤ M) (hvM : ∀ u, |v u| ≤ M) :
    0 ≤ ∑' N : ℕ+, ∫ u, fiber N u * divisorEnergy N (fun m => v (u - Real.log m)) := by
  rw [← primeEnergy_eq_tsum_divisorEnergy hv hM hvM]
  exact tsum_nonneg (fun d => integral_nonneg (fun u => phiDoobPrimeJump_nonneg v d u))

end

end RHTower.PhiDivisorEnergy
