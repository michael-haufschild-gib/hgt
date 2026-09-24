import GaloisForLFunctions.RHTower.EstermannEdgeBounds
import GaloisForLFunctions.RHTower.EstermannStripExpBound
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# The convexity bound for Estermann's zeta function

The entire completion `(s-1)² D(s, a/q)` grows polynomially on `Re s = 2` and on `Re s = -1`, and
at most like `e^{(π+2)|t|}` in between.  Dividing by `(s+2)^N` makes the two edge bounds constant
without affecting the growth class, so Phragmén--Lindelöf applies on a strip of width three, where
the admissible exponent `c` may be taken to be `1/2 < π/3`.  The conclusion is a single polynomial
bound valid on the whole closed strip.
-/

open Complex Filter Set Asymptotics

namespace RHTower

noncomputable section

variable {q : ℕ} [NeZero q]

/-- On the strip the shift `s + 2` is comparable with the height. -/
theorem one_add_abs_im_le_two_mul_norm {z : ℂ} (h : -1 ≤ z.re) : 1 + |z.im| ≤ 2 * ‖z + 2‖ := by
  have hre : (z + 2).re = z.re + 2 := by simp
  have him : (z + 2).im = z.im := by simp
  have h1 : |(z + 2).re| ≤ ‖z + 2‖ := Complex.abs_re_le_norm _
  have h2 : |(z + 2).im| ≤ ‖z + 2‖ := Complex.abs_im_le_norm _
  rw [hre] at h1
  rw [him] at h2
  have h3 : (1 : ℝ) ≤ |z.re + 2| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  linarith

theorem shift_ne_zero {z : ℂ} (h : -(3 : ℝ) / 2 < z.re) : z + 2 ≠ 0 := by
  intro hcon
  have hc := congrArg Complex.re hcon
  simp only [Complex.add_re, Complex.re_ofNat, Complex.zero_re] at hc
  linarith

/-- **The convexity bound.**  One constant and one exponent for the whole closed strip
`-1 ≤ Re s ≤ 2`. -/
theorem exists_bound_norm_estermannEntire_strip (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖estermannEntire q ((a : ZMod q)) s‖ ≤ C * (1 + |s.im|) ^ N := by
  classical
  obtain ⟨CR, hCR0, hCR⟩ := exists_bound_norm_estermannEntire_right q a
  obtain ⟨CL, NL, hCL0, hCL⟩ := exists_bound_norm_estermannEntire_left q a
  obtain ⟨K, hK0, hK⟩ := exists_bound_norm_estermannZeta_strip_exp q ((a : ZMod q)) (-1) 2
    (by norm_num)
  set f : ℂ → ℂ := estermannEntire q ((a : ZMod q)) with hf
  set N : ℕ := NL + 2 with hN
  set Cb : ℝ := (CR + CL) * 2 ^ N with hCb
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  set g : ℂ → ℂ := fun s => f s / (s + 2) ^ N with hg
  have hfdiff : Differentiable ℂ f := differentiable_estermannEntire a
  -- differentiability of `g` right of `-3/2`
  have hgdiff : ∀ z : ℂ, -(3 : ℝ) / 2 < z.re → DifferentiableAt ℂ g z := by
    intro z hz
    refine (hfdiff z).div (((differentiable_id.add_const (2 : ℂ)).pow N) z) ?_
    exact pow_ne_zero _ (shift_ne_zero hz)
  -- the edge bound, on both edges, in terms of the height
  have hedge : ∀ z : ℂ, z.re = -1 ∨ z.re = 2 → ‖f z‖ ≤ (CR + CL) * (1 + |z.im|) ^ N := by
    intro z hz
    have hbase : (1 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
    rcases hz with hz | hz
    · have hzz : z = ((-1 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I := by
        conv_lhs => rw [← Complex.re_add_im z]
        rw [hz]
      have h := hCL z.im
      rw [← hzz] at h
      have hmono : (1 + |z.im|) ^ NL ≤ (1 + |z.im|) ^ N :=
        pow_le_pow_right₀ hbase (by omega)
      have hpos : (0 : ℝ) ≤ (1 + |z.im|) ^ N := by positivity
      nlinarith [h, hmono, hCL0, hCR0]
    · have hzz : z = ((2 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I := by
        conv_lhs => rw [← Complex.re_add_im z]
        rw [hz]
      have h := hCR z.im
      rw [← hzz] at h
      have hmono : (1 + |z.im|) ^ (2 : ℕ) ≤ (1 + |z.im|) ^ N :=
        pow_le_pow_right₀ hbase (by omega)
      have hpos : (0 : ℝ) ≤ (1 + |z.im|) ^ N := by positivity
      nlinarith [h, hmono, hCL0, hCR0]
  -- the edge bound for `g` is constant
  have hgedge : ∀ z : ℂ, z.re = -1 ∨ z.re = 2 → ‖g z‖ ≤ Cb := by
    intro z hz
    have hre1 : -1 ≤ z.re := by rcases hz with h | h <;> linarith [h.le, h.ge]
    have hshift : (0 : ℝ) < ‖z + 2‖ := by
      refine norm_pos_iff.mpr (shift_ne_zero (by linarith))
    have hcmp : 1 + |z.im| ≤ 2 * ‖z + 2‖ := one_add_abs_im_le_two_mul_norm hre1
    have hpow : (1 + |z.im|) ^ N ≤ (2 * ‖z + 2‖) ^ N :=
      pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) hcmp N
    rw [hg]
    simp only [norm_div, norm_pow]
    rw [div_le_iff₀ (by positivity)]
    calc ‖f z‖ ≤ (CR + CL) * (1 + |z.im|) ^ N := hedge z hz
      _ ≤ (CR + CL) * (2 * ‖z + 2‖) ^ N := by
          refine mul_le_mul_of_nonneg_left hpow (by linarith)
      _ = Cb * ‖z + 2‖ ^ N := by rw [hCb, mul_pow]; ring
  refine ⟨Cb * 4 ^ N, N, by positivity, fun s h0 h1 => ?_⟩
  -- Phragmén–Lindelöf
  have hPL : ‖g s‖ ≤ Cb := by
    refine PhragmenLindelof.vertical_strip (f := g) (a := (-1 : ℝ)) (b := (2 : ℝ)) (C := Cb)
      ⟨?_, ?_⟩ ?_ (fun z hz => hgedge z (Or.inl hz)) (fun z hz => hgedge z (Or.inr hz)) h0 h1
    · intro z hz
      exact (hgdiff z (by have : (-1 : ℝ) < z.re := hz.1; linarith)).differentiableWithinAt
    · have hsub : closure (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) ⊆ Complex.re ⁻¹' Icc (-1 : ℝ) 2 := by
        refine closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) ?_
        exact IsClosed.preimage Complex.continuous_re isClosed_Icc
      refine fun z hz => ((hgdiff z ?_).continuousAt.continuousWithinAt)
      have := (hsub hz).1
      linarith
    · refine ⟨1 / 2, ?_, 2 * (Real.pi + 2), ?_⟩
      · rw [show (2 : ℝ) - (-1) = 3 by norm_num]
        rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
        linarith [Real.pi_gt_three]
      · refine Asymptotics.isBigO_iff.mpr ⟨9 * K, ?_⟩
        have hmem : {z : ℂ | 2 ≤ |z.im|} ∈
            comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) := by
          refine Filter.mem_inf_of_left ?_
          exact Filter.mem_comap.mpr ⟨Ici (2 : ℝ), Ici_mem_atTop 2, fun z hz => hz⟩
        have hmemU : (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) ∈
            comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) :=
          Filter.mem_inf_of_right (Filter.mem_principal_self _)
        filter_upwards [hmem, hmemU] with z hz hzU
        have hz2 : (2 : ℝ) ≤ |z.im| := hz
        have hzre : z.re ∈ Ioo (-1 : ℝ) 2 := hzU
        have hne : z ≠ 1 := by
          intro hcon
          rw [hcon] at hz2
          norm_num at hz2
        have hD : ‖estermannZeta q ((a : ZMod q)) z‖ ≤ K * Real.exp (Real.pi * |z.im|) :=
          hK z hzre.1.le hzre.2.le hz2
        have hsm : ‖z - 1‖ ≤ 3 + |z.im| := by
          have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
          have hre : (z - 1).re = z.re - 1 := by simp
          have him : (z - 1).im = z.im := by simp
          rw [hre, him] at h
          have : |z.re - 1| ≤ 3 := by
            rw [abs_le]; constructor <;> linarith [hzre.1, hzre.2]
          linarith
        have hfz : ‖f z‖ ≤ (3 + |z.im|) ^ (2 : ℕ) * (K * Real.exp (Real.pi * |z.im|)) := by
          rw [hf, estermannEntire_eq _ hne, norm_mul, norm_pow]
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hsm 2) hD (norm_nonneg _)
            (by positivity)
        have hgz : ‖g z‖ ≤ ‖f z‖ := by
          rw [hg]
          simp only [norm_div, norm_pow]
          refine div_le_self (norm_nonneg _) ?_
          have h1' : (1 : ℝ) ≤ ‖z + 2‖ := by
            have := one_add_abs_im_le_two_mul_norm (z := z) (by linarith [hzre.1])
            linarith [abs_nonneg z.im]
          exact one_le_pow₀ h1'
        -- turn the polynomial factor into an exponential
        set u : ℝ := |z.im| with hu
        have hu0 : (0 : ℝ) ≤ u := abs_nonneg _
        have hexp1 : (3 : ℝ) + u ≤ 3 * Real.exp u := by
          have := Real.add_one_le_exp u
          linarith
        have hsq : (3 + u) ^ (2 : ℕ) ≤ 9 * Real.exp (2 * u) := by
          have h3 : (0 : ℝ) ≤ 3 + u := by linarith
          calc (3 + u) ^ (2 : ℕ) ≤ (3 * Real.exp u) ^ (2 : ℕ) :=
                pow_le_pow_left₀ h3 hexp1 2
            _ = 9 * (Real.exp u * Real.exp u) := by ring
            _ = 9 * Real.exp (2 * u) := by rw [← Real.exp_add]; congr 2; ring
        have hfin : ‖f z‖ ≤ 9 * K * Real.exp ((Real.pi + 2) * u) := by
          refine hfz.trans ?_
          calc (3 + u) ^ (2 : ℕ) * (K * Real.exp (Real.pi * u))
              ≤ (9 * Real.exp (2 * u)) * (K * Real.exp (Real.pi * u)) := by
                refine mul_le_mul_of_nonneg_right hsq (by positivity)
            _ = 9 * K * (Real.exp (2 * u) * Real.exp (Real.pi * u)) := by ring
            _ = 9 * K * Real.exp ((Real.pi + 2) * u) := by
                rw [← Real.exp_add]; congr 2; ring
        have hdom : Real.exp ((Real.pi + 2) * u)
            ≤ Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * u)) := by
          refine Real.exp_le_exp.mpr ?_
          have hhalf : (1 / 2 : ℝ) * u ≤ Real.exp (1 / 2 * u) := by
            have := Real.add_one_le_exp ((1 / 2 : ℝ) * u)
            linarith
          nlinarith [Real.pi_pos, hhalf]
        have hnormg : ‖Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * |z.im|))‖
            = Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * |z.im|)) :=
          Real.norm_of_nonneg (Real.exp_pos _).le
        rw [hnormg]
        calc ‖g z‖ ≤ ‖f z‖ := hgz
          _ ≤ 9 * K * Real.exp ((Real.pi + 2) * u) := hfin
          _ ≤ 9 * K * Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * u)) := by
              refine mul_le_mul_of_nonneg_left hdom (by positivity)
  -- undo the division
  have hshift : (0 : ℝ) < ‖s + 2‖ := norm_pos_iff.mpr (shift_ne_zero (by linarith))
  have hfs : ‖f s‖ = ‖g s‖ * ‖s + 2‖ ^ N := by
    rw [hg]
    simp only [norm_div, norm_pow]
    field_simp
  have hbnd : ‖s + 2‖ ≤ 4 * (1 + |s.im|) := by
    have h := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hre : (s + 2).re = s.re + 2 := by simp
    have him : (s + 2).im = s.im := by simp
    rw [hre, him] at h
    have : |s.re + 2| ≤ 4 := by rw [abs_le]; constructor <;> linarith
    linarith [abs_nonneg s.im]
  rw [hfs]
  calc ‖g s‖ * ‖s + 2‖ ^ N ≤ Cb * (4 * (1 + |s.im|)) ^ N := by
        refine mul_le_mul hPL (pow_le_pow_left₀ (norm_nonneg _) hbnd N) (by positivity) hCb0
    _ = Cb * 4 ^ N * (1 + |s.im|) ^ N := by rw [mul_pow]; ring

end

end RHTower
