import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomMellinOffLineCountermodel

open Complex MeasureTheory

namespace RHTower

noncomputable section

private def wallWeight : ℝ := Real.exp ((1 / 8 : ℝ) * Real.log 2)
private def wallScale : ℝ := Real.exp ((5 / 8 : ℝ) * Real.log 2)

private theorem wallScale_pos : 0 < wallScale := Real.exp_pos _

private theorem counterWeight_eq_wallWeight_mul_wallScale :
    thetaTwoAtomCounterWeight = wallWeight * wallScale := by
  unfold thetaTwoAtomCounterWeight wallWeight wallScale
  rw [← Real.exp_add]
  congr 1
  ring

private def wallAtom (x y : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then x else y

private def wallAutocorrelation (x y : ℝ) (r : ℚ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    if ((i.val + 1 : ℕ) : ℚ) / ((j.val + 1 : ℕ) : ℚ) = r then
      wallAtom x y i * wallAtom x y j else 0

private theorem wallAutocorrelation_flip (x y : ℝ) (r : ℚ) :
    wallAutocorrelation x y r = wallAutocorrelation y x r := by
  classical
  simp [wallAutocorrelation, wallAtom, Fin.sum_univ_two]
  ring_nf

private def sourceWallAutocorrelation (c1 c2 : ℝ) (r : ℚ) : ℝ :=
  wallAutocorrelation c1 (c2 / wallScale) r

theorem thetaTwoAtomWallAutocorrelation_factorFlip (r : ℚ) :
    sourceWallAutocorrelation 1 thetaTwoAtomCounterWeight r =
      sourceWallAutocorrelation wallWeight wallScale r := by
  rw [sourceWallAutocorrelation, sourceWallAutocorrelation,
    counterWeight_eq_wallWeight_mul_wallScale]
  rw [mul_div_cancel_right₀ _ wallScale_pos.ne', div_self wallScale_pos.ne']
  exact wallAutocorrelation_flip 1 wallWeight r

private def flippedSeed (t : ℝ) : ℂ :=
  (wallWeight : ℂ) * (thetaCuspSeed t : ℂ) +
    (wallScale : ℂ) * (thetaCuspSeed (2 * t) : ℂ)

private theorem flippedSeed_mellin_factor {s : ℂ} (hs : 0 < s.re) :
    mellin flippedSeed s =
      archFactor s * ((wallWeight : ℂ) + (wallScale : ℂ) * (2 : ℂ) ^ (-s)) := by
  let f : ℝ → ℂ := fun t => (thetaCuspSeed t : ℂ)
  have hf : MellinConvergent f s := mellinConvergent_thetaCuspSeed hs
  have hf2 : MellinConvergent (fun t => f (2 * t)) s :=
    (MellinConvergent.comp_mul_left (f := f) (s := s)
      (by norm_num : (0 : ℝ) < 2)).2 hf
  have hsum := hasMellin_add (hf.const_smul (wallWeight : ℂ))
    (hf2.const_smul (wallScale : ℂ))
  have hfactor : mellin flippedSeed s =
      (wallWeight : ℂ) * mellin f s +
        (wallScale : ℂ) * mellin (fun t => f (2 * t)) s := by
    calc
      mellin flippedSeed s =
          mellin (fun t => (wallWeight : ℂ) • f t +
            (wallScale : ℂ) • f (2 * t)) s := rfl
      _ = mellin (fun t => (wallWeight : ℂ) • f t) s +
          mellin (fun t => (wallScale : ℂ) • f (2 * t)) s := hsum.2
      _ = _ := by rw [mellin_const_smul, mellin_const_smul]; simp [smul_eq_mul]
  rw [hfactor, mellin_comp_mul_left f s (by norm_num : (0 : ℝ) < 2),
    mellin_thetaCuspSeed_eq_archFactor hs]
  simp only [smul_eq_mul, Complex.ofReal_ofNat]
  ring

private def linePoint : ℂ :=
  (1 / 2 : ℝ) + ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I

private theorem linePoint_re : linePoint.re = 1 / 2 := by
  unfold linePoint
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_one,
    add_zero]

private theorem linePoint_power :
    (wallWeight : ℂ) * (2 : ℂ) ^ linePoint = -(wallScale : ℂ) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog2 : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog2]
  have harg : (Real.log 2 : ℂ) * linePoint =
      ((1 / 2 * Real.log 2 : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
    unfold linePoint
    push_cast
    field_simp [hlog, hlogC]
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
  rw [show ((1 / 2 * Real.log 2 : ℝ) : ℂ) =
      (((1 / 2 : ℝ) * Real.log 2 : ℝ) : ℂ) by rfl,
    ← Complex.ofReal_exp]
  unfold wallWeight wallScale
  push_cast
  have hexp : (1 / 8 : ℂ) * (Real.log 2 : ℂ) +
      (1 / 2 : ℂ) * (Real.log 2 : ℂ) =
        (5 / 8 : ℂ) * (Real.log 2 : ℂ) := by ring
  calc
    Complex.exp ((1 / 8 : ℂ) * (Real.log 2 : ℂ)) *
        (Complex.exp ((1 / 2 : ℂ) * (Real.log 2 : ℂ)) * -1) =
        -Complex.exp ((1 / 8 : ℂ) * (Real.log 2 : ℂ) +
          (1 / 2 : ℂ) * (Real.log 2 : ℂ)) := by rw [Complex.exp_add]; ring
    _ = -Complex.exp ((5 / 8 : ℂ) * (Real.log 2 : ℂ)) := by rw [hexp]

private theorem flippedSeed_mellin_line_zero :
    linePoint.re = 1 / 2 ∧ mellin flippedSeed linePoint = 0 := by
  have hs : 0 < linePoint.re := by rw [linePoint_re]; norm_num
  refine ⟨linePoint_re, ?_⟩
  rw [flippedSeed_mellin_factor hs]
  have hc : (2 : ℂ) ^ linePoint ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hzero : (wallWeight : ℂ) + (wallScale : ℂ) * (2 : ℂ) ^ (-linePoint) = 0 := by
    rw [Complex.cpow_neg]
    calc
      (wallWeight : ℂ) + (wallScale : ℂ) * ((2 : ℂ) ^ linePoint)⁻¹ =
          ((wallWeight : ℂ) * (2 : ℂ) ^ linePoint + (wallScale : ℂ)) /
            ((2 : ℂ) ^ linePoint) := by field_simp [hc]
      _ = 0 := by rw [linePoint_power]; simp
  rw [hzero]
  ring

end
end RHTower
