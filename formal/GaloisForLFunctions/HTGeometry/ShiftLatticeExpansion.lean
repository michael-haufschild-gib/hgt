import GaloisForLFunctions.HTGeometry.ShiftLatticeThetaSeries

/-!
# The shift-lattice expansion inside the upper half plane

Translating the argument of the degree-`d` theta series by `ζ` multiplies each
term by `e(ζ n^{1/d})`, and expanding that exponential shifts the spectral
variable down the lattice `s - k/d`.  Inside the upper half plane the resulting
double family is absolutely summable whenever `|ζ|` is smaller than the height of
the base point: summing the exponential series back up only replaces the decay
rate `Im z₀` by `Im z₀ - |ζ|`, which is still positive.

Fubini therefore gives the shift-lattice expansion

`Θ(s, z₀ + ζ) = ∑_k (2πiζ)^k · Θ(s - k/d, z₀) / k!`

with no continuation and no contour shifting.  Its radius of convergence is at
least the height of the base point, so the factorially normalized spectral
family satisfies `limsup_k ‖Θ(s-k/d, z₀)/k!‖^{1/k} ≤ 1/(2π Im z₀)`.
-/

open Complex Filter Topology
open scoped BigOperators ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-- The geometric factor of the shift-lattice expansion. -/
noncomputable def shiftFactor : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem norm_shiftFactor : ‖shiftFactor‖ = 2 * Real.pi := by
  rw [shiftFactor, norm_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

theorem shiftFactor_ne_zero : shiftFactor ≠ 0 := by
  intro h
  have := norm_shiftFactor
  rw [h, norm_zero] at this
  have := Real.pi_pos
  linarith

/-- The factorially normalized spectral family of the shift lattice. -/
noncomputable def shiftLatticeCoeff (a : ℕ → ℂ) (d : ℝ) (s z₀ : ℂ) (k : ℕ) : ℂ :=
  thetaSeries a d (s - (k : ℂ) / (d : ℂ)) z₀ / (Nat.factorial k : ℂ)

section Expansion

variable {a : ℕ → ℂ} {C B d : ℝ}

/-- The spectral shift by `k/d` is multiplication by the `k`-th power of the
lattice generator. -/
theorem natCast_cpow_shift (n k : ℕ) {d : ℝ} (hd : 0 < d) :
    ((n : ℂ)) ^ ((k : ℂ) / (d : ℂ)) = ((((n : ℝ) ^ (1 / d) : ℝ)) : ℂ) ^ k := by
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd0 : (d : ℝ) ≠ 0 := hd.ne'
  rw [← Complex.ofReal_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / d)) k,
    ← Real.rpow_mul hnR, Complex.ofReal_cpow hnR]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast]
  field_simp

/-- **The termwise expansion.**  At each index the translated term is the
exponential series in the lattice generator. -/
theorem hasSum_thetaTerm_shift {n : ℕ} (hn : 0 < n) (hd : 0 < d) (s z₀ ζ : ℂ) :
    HasSum (fun k : ℕ => (shiftFactor * ζ) ^ k / (Nat.factorial k : ℂ)
        * thetaTerm a d (s - (k : ℂ) / (d : ℂ)) z₀ n)
      (thetaTerm a d s (z₀ + ζ) n) := by
  have hnC : ((n : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hn.ne'
  set t : ℝ := (n : ℝ) ^ (1 / d) with ht
  set Cst : ℂ := a n * (n : ℂ) ^ (-s)
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z₀ * (t : ℂ)) with hCst
  have hterm : ∀ k : ℕ, (shiftFactor * ζ) ^ k / (Nat.factorial k : ℂ)
      * thetaTerm a d (s - (k : ℂ) / (d : ℂ)) z₀ n
      = Cst * ((shiftFactor * ζ * (t : ℂ)) ^ k / (Nat.factorial k : ℂ)) := by
    intro k
    rw [thetaTerm, if_neg hn.ne']
    have hcpow : ((n : ℂ)) ^ (-(s - (k : ℂ) / (d : ℂ)))
        = (n : ℂ) ^ (-s) * ((n : ℂ)) ^ ((k : ℂ) / (d : ℂ)) := by
      rw [← Complex.cpow_add _ _ hnC]
      congr 1
      ring
    rw [hcpow, natCast_cpow_shift n k hd, ← ht, hCst]
    ring
  have hexp : HasSum
      (fun k : ℕ => (shiftFactor * ζ * (t : ℂ)) ^ k / (Nat.factorial k : ℂ))
      (Complex.exp (shiftFactor * ζ * (t : ℂ))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hgoal : thetaTerm a d s (z₀ + ζ) n
      = Cst * Complex.exp (shiftFactor * ζ * (t : ℂ)) := by
    have hsplit : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z₀ + ζ) * (t : ℂ))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z₀ * (t : ℂ))
          * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ζ * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [thetaTerm, if_neg hn.ne', ← ht, hsplit, hCst, shiftFactor]
    ring
  rw [hgoal]
  simpa only [hterm] using hexp.mul_left Cst

/-- The exact modulus of one member of the double family. -/
theorem norm_shiftDouble {n : ℕ} (hn : 0 < n) (hd : 0 < d) (s z₀ ζ : ℂ) (k : ℕ) :
    ‖(shiftFactor * ζ) ^ k / (Nat.factorial k : ℂ)
        * thetaTerm a d (s - (k : ℂ) / (d : ℂ)) z₀ n‖
      = ‖thetaTerm a d s z₀ n‖
        * ((2 * Real.pi * ‖ζ‖ * ((n : ℝ) ^ (1 / d))) ^ k / (Nat.factorial k : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : (s - (k : ℂ) / (d : ℂ)).re = s.re - (k : ℝ) / d := by
    have hcast : ((k : ℂ) / (d : ℂ)) = (((k : ℝ) / d : ℝ) : ℂ) := by push_cast; ring
    rw [Complex.sub_re, hcast, Complex.ofReal_re]
  rw [norm_mul, norm_div, norm_pow, norm_mul, norm_shiftFactor,
    Complex.norm_natCast, norm_thetaTerm a d _ z₀ hn, norm_thetaTerm a d s z₀ hn,
    hre]
  have hsplit : (n : ℝ) ^ (-(s.re - (k : ℝ) / d))
      = (n : ℝ) ^ (-s.re) * ((n : ℝ) ^ (1 / d)) ^ k := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / d)) k, ← Real.rpow_mul hnR.le,
      ← Real.rpow_add hnR]
    congr 1
    field_simp
    ring
  rw [hsplit, mul_pow]
  ring

/-- **Absolute convergence of the double family.**  Inside the height of the base
point the shift-lattice double family is absolutely summable. -/
theorem summable_norm_shiftDouble {C B : ℝ} (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B)
    (hd : 0 < d) (s z₀ ζ : ℂ) (hζ : ‖ζ‖ < z₀.im) :
    Summable fun p : ℕ × ℕ => ‖(shiftFactor * ζ) ^ p.2 / (Nat.factorial p.2 : ℂ)
      * thetaTerm a d (s - (p.2 : ℂ) / (d : ℂ)) z₀ p.1‖ := by
  have hzpos : 0 < z₀.im := lt_of_le_of_lt (norm_nonneg ζ) hζ
  set y : ℝ := z₀.im - ‖ζ‖ with hy
  have hypos : 0 < y := by rw [hy]; linarith
  set z' : ℂ := Complex.I * ((y : ℝ) : ℂ) with hz'
  have hz'im : z'.im = y := by rw [hz']; simp
  have hz'pos : 0 < z'.im := by rw [hz'im]; exact hypos
  refine (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr ⟨fun n => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · refine ((Real.summable_pow_div_factorial
        (2 * Real.pi * ‖ζ‖ * ((n : ℝ) ^ (1 / d)))).mul_left
        ‖thetaTerm a d s z₀ n‖).congr fun k => ?_
      exact (norm_shiftDouble hn hd s z₀ ζ k).symm
  · refine (summable_norm_thetaTerm_of_im_pos ha hd s z' hz'pos).congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hexp : HasSum
          (fun k : ℕ => (2 * Real.pi * ‖ζ‖ * ((n : ℝ) ^ (1 / d))) ^ k
            / (Nat.factorial k : ℝ))
          (Real.exp (2 * Real.pi * ‖ζ‖ * ((n : ℝ) ^ (1 / d)))) := by
        rw [Real.exp_eq_exp_ℝ]
        exact NormedSpace.expSeries_div_hasSum_exp _
      have hfib : (∑' k : ℕ, ‖(shiftFactor * ζ) ^ k / (Nat.factorial k : ℂ)
            * thetaTerm a d (s - (k : ℂ) / (d : ℂ)) z₀ n‖)
          = ‖thetaTerm a d s z₀ n‖
            * Real.exp (2 * Real.pi * ‖ζ‖ * ((n : ℝ) ^ (1 / d))) := by
        rw [tsum_congr fun k => norm_shiftDouble hn hd s z₀ ζ k]
        exact (hexp.mul_left _).tsum_eq
      rw [hfib, norm_thetaTerm a d s z₀ hn, norm_thetaTerm a d s z' hn, hz'im,
        show -(2 * Real.pi * y * ((n : ℝ) ^ (1 / d)))
            = -(2 * Real.pi * z₀.im * ((n : ℝ) ^ (1 / d)))
              + 2 * Real.pi * ‖ζ‖ * ((n : ℝ) ^ (1 / d)) from by rw [hy]; ring,
        Real.exp_add]
      ring

/-- Absolute convergence of the double family, unnormed form. -/
theorem summable_shiftDouble {C B : ℝ} (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B)
    (hd : 0 < d) (s z₀ ζ : ℂ) (hζ : ‖ζ‖ < z₀.im) :
    Summable fun p : ℕ × ℕ => (shiftFactor * ζ) ^ p.2 / (Nat.factorial p.2 : ℂ)
      * thetaTerm a d (s - (p.2 : ℂ) / (d : ℂ)) z₀ p.1 :=
  (summable_norm_shiftDouble ha hd s z₀ ζ hζ).of_norm

/-- Each `k`-fibre of the double family sums to one term of the expansion. -/
theorem hasSum_shiftDouble_fiber {C B : ℝ} (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B)
    (hd : 0 < d) (s z₀ ζ : ℂ) (hz : 0 < z₀.im) (k : ℕ) :
    HasSum (fun n : ℕ => (shiftFactor * ζ) ^ k / (Nat.factorial k : ℂ)
        * thetaTerm a d (s - (k : ℂ) / (d : ℂ)) z₀ n)
      ((shiftFactor * ζ) ^ k * shiftLatticeCoeff a d s z₀ k) := by
  have hs := (summable_thetaTerm_of_im_pos ha hd (s - (k : ℂ) / (d : ℂ)) z₀ hz).hasSum
  have heq : (shiftFactor * ζ) ^ k / (Nat.factorial k : ℂ)
      * thetaSeries a d (s - (k : ℂ) / (d : ℂ)) z₀
      = (shiftFactor * ζ) ^ k * shiftLatticeCoeff a d s z₀ k := by
    rw [shiftLatticeCoeff]
    ring
  rw [← heq]
  exact hs.mul_left _

set_option maxHeartbeats 1600000 in
/-- **The shift-lattice expansion inside the upper half plane.**  Translating the
base point by `ζ` expands the theta series along the spectral lattice `s - k/d`,
with geometric factor `2πiζ`.  No continuation and no contour shifting are
involved: the double family is absolutely summable. -/
theorem hasSum_shiftLatticeExpansion {C B : ℝ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B) (hd : 0 < d) (s z₀ ζ : ℂ)
    (hζ : ‖ζ‖ < z₀.im) :
    HasSum (fun k : ℕ => (shiftFactor * ζ) ^ k * shiftLatticeCoeff a d s z₀ k)
      (thetaSeries a d s (z₀ + ζ)) := by
  have hzpos : 0 < z₀.im := lt_of_le_of_lt (norm_nonneg ζ) hζ
  have hsum := summable_shiftDouble ha hd s z₀ ζ hζ
  have hfib : ∀ n : ℕ, HasSum
      (fun k : ℕ => (shiftFactor * ζ) ^ k / (Nat.factorial k : ℂ)
        * thetaTerm a d (s - (k : ℂ) / (d : ℂ)) z₀ n)
      (thetaTerm a d s (z₀ + ζ) n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [thetaTerm_zero, mul_zero]
      exact hasSum_zero
    · exact hasSum_thetaTerm_shift hn hd s z₀ ζ
  have htotal := hsum.hasSum.prod_fiberwise hfib
  have hval : (∑' p : ℕ × ℕ, (shiftFactor * ζ) ^ p.2 / (Nat.factorial p.2 : ℂ)
      * thetaTerm a d (s - (p.2 : ℂ) / (d : ℂ)) z₀ p.1)
      = thetaSeries a d s (z₀ + ζ) := htotal.tsum_eq.symm
  have hswap : HasSum (fun p : ℕ × ℕ => (shiftFactor * ζ) ^ p.1
      / (Nat.factorial p.1 : ℂ)
      * thetaTerm a d (s - (p.1 : ℂ) / (d : ℂ)) z₀ p.2)
      (∑' p : ℕ × ℕ, (shiftFactor * ζ) ^ p.2 / (Nat.factorial p.2 : ℂ)
        * thetaTerm a d (s - (p.2 : ℂ) / (d : ℂ)) z₀ p.1) :=
    ((Equiv.prodComm ℕ ℕ).hasSum_iff).mpr hsum.hasSum
  have hfinal := hswap.prod_fiberwise
    (fun k => hasSum_shiftDouble_fiber ha hd s z₀ ζ hzpos k)
  rwa [hval] at hfinal

end Expansion

section RadiusBound

variable {a : ℕ → ℂ} {d : ℝ}

/-- The geometrically weighted spectral family is absolutely summable strictly
inside the height of the base point. -/
theorem summable_norm_shiftLatticeCoeff_mul_pow {C B : ℝ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B) (hd : 0 < d) (s z₀ : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < z₀.im) :
    Summable fun k : ℕ =>
      ‖shiftFactor ^ k * shiftLatticeCoeff a d s z₀ k‖ * r ^ k := by
  have hzpos : 0 < z₀.im := lt_of_le_of_lt hr0 hr
  have hζ : ‖((r : ℝ) : ℂ)‖ < z₀.im := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr
  have hnorm := summable_norm_shiftDouble ha hd s z₀ ((r : ℝ) : ℂ) hζ
  have hswap : Summable fun p : ℕ × ℕ =>
      ‖(shiftFactor * ((r : ℝ) : ℂ)) ^ p.1 / (Nat.factorial p.1 : ℂ)
        * thetaTerm a d (s - (p.1 : ℂ) / (d : ℂ)) z₀ p.2‖ :=
    ((Equiv.prodComm ℕ ℕ).summable_iff).mpr hnorm
  have hk : Summable fun k : ℕ => ∑' n : ℕ,
      ‖(shiftFactor * ((r : ℝ) : ℂ)) ^ k / (Nat.factorial k : ℂ)
        * thetaTerm a d (s - (k : ℂ) / (d : ℂ)) z₀ n‖ :=
    ((summable_prod_of_nonneg (fun p => norm_nonneg _)).mp hswap).2
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hk
  have hfibre := hasSum_shiftDouble_fiber ha hd s z₀ ((r : ℝ) : ℂ) hzpos k
  have hfsum : Summable fun n : ℕ =>
      (shiftFactor * ((r : ℝ) : ℂ)) ^ k / (Nat.factorial k : ℂ)
        * thetaTerm a d (s - (k : ℂ) / (d : ℂ)) z₀ n := hfibre.summable
  have hle := norm_tsum_le_tsum_norm hfsum.norm
  rw [hfibre.tsum_eq] at hle
  have hrw : ‖(shiftFactor * ((r : ℝ) : ℂ)) ^ k * shiftLatticeCoeff a d s z₀ k‖
      = ‖shiftFactor ^ k * shiftLatticeCoeff a d s z₀ k‖ * r ^ k := by
    simp only [mul_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    ring
  rw [← hrw]
  exact hle

/-- **The interior radius bound.**  The shift-lattice expansion converges on the
whole disk of radius the height of the base point, so the factorially normalized
spectral family grows no faster than `1/(2π Im z₀)`. -/
theorem hadamardLimsup_shiftLatticeCoeff_le {C B : ℝ}
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (n : ℝ) ^ B) (hd : 0 < d) (s z₀ : ℂ)
    (hz : 0 < z₀.im) :
    hadamardLimsup (shiftLatticeCoeff a d s z₀)
      ≤ ENNReal.ofReal (1 / (2 * Real.pi * z₀.im)) := by
  set q : ℕ → ℂ := fun k => shiftFactor ^ k * shiftLatticeCoeff a d s z₀ k with hq
  have hrad : ENNReal.ofReal z₀.im
      ≤ (FormalMultilinearSeries.ofScalars ℂ q).radius := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hcrad, hc⟩ := exists_between hcon
    refine absurd ?_ (not_le.mpr hcrad)
    have hctop : c ≠ ⊤ := ne_top_of_lt hc
    have hcre : c.toReal < z₀.im := by
      have := (ENNReal.toReal_lt_toReal hctop ENNReal.ofReal_ne_top).mpr hc
      rwa [ENNReal.toReal_ofReal hz.le] at this
    have hcnn : 0 ≤ c.toReal := ENNReal.toReal_nonneg
    have hsum := summable_norm_shiftLatticeCoeff_mul_pow ha hd s z₀ hcnn hcre
    have hle := (FormalMultilinearSeries.ofScalars ℂ q).le_radius_of_summable_nnnorm
      (r := c.toReal.toNNReal) ?_
    · rwa [show ((c.toReal.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal c.toReal from rfl,
        ENNReal.ofReal_toReal hctop] at hle
    · refine (NNReal.summable_coe).mp ?_
      refine hsum.congr fun k => ?_
      rw [NNReal.coe_mul, coe_nnnorm, FormalMultilinearSeries.ofScalars_norm,
        NNReal.coe_pow, Real.coe_toNNReal _ hcnn]
  rw [radius_ofScalars_eq_inv_hadamardLimsup, hadamardLimsup_geometric] at hrad
  have hA : ((‖shiftFactor‖₊ : ℝ≥0∞)) ≠ 0 := by
    simp [shiftFactor_ne_zero]
  have hAtop : ((‖shiftFactor‖₊ : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
  have h1 : ((‖shiftFactor‖₊ : ℝ≥0∞))
      * hadamardLimsup (shiftLatticeCoeff a d s z₀)
      ≤ (ENNReal.ofReal z₀.im)⁻¹ := ENNReal.le_inv_iff_le_inv.mp hrad
  have hpi : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have hcoe : ((‖shiftFactor‖₊ : ℝ≥0∞)) = ENNReal.ofReal (2 * Real.pi) := by
    rw [← norm_shiftFactor, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    rfl
  rw [hcoe, ← ENNReal.ofReal_inv_of_pos hz, mul_comm] at h1
  have hne : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpi
  have h2 := (ENNReal.le_div_iff_mul_le
    (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)).mpr h1
  refine h2.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos hpi]
  congr 1
  field_simp

end RadiusBound

end GaloisForLFunctions.HTGeometry
