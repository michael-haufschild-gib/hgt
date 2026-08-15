import GaloisForLFunctions.HTGeometry.PowerCanonicalProductLogDeriv
import GaloisForLFunctions.HTGeometry.RightHalfPlaneSpace

/-!
# The power canonical product on the right half-plane

The zeros of `W_a` are the negative reals `-n^a`, so `W_a` has no zero where the real part is
positive.  The right half-plane is open, convex and infinite, and it carries the analytic branch of
`z^{1/a}`, so it is a domain on which the whole Barnes decomposition of `x W_a'/W_a` lives.
-/

open Complex

namespace HTGeometry

open GaloisForLFunctions.HTGeometry

variable {s : ℝ}

theorem convex_rightHalfPlane : Convex ℝ rightHalfPlane := by
  refine convex_halfSpace_re_gt 0

theorem isPreconnected_rightHalfPlane : IsPreconnected rightHalfPlane :=
  convex_rightHalfPlane.isPreconnected

theorem rightHalfPlane_nonempty : rightHalfPlane.Nonempty :=
  ⟨1, by simp [rightHalfPlane]⟩

theorem ofReal_mem_rightHalfPlane {x : ℝ} (hx : 0 < x) : ((x : ℝ) : ℂ) ∈ rightHalfPlane := by
  simpa [rightHalfPlane] using hx

theorem rightHalfPlane_infinite : rightHalfPlane.Infinite := by
  have hinj : Set.InjOn (fun x : ℝ => ((x : ℝ) : ℂ)) (Set.Ioi (0 : ℝ)) :=
    fun a _ b _ h => Complex.ofReal_injective h
  have himg : ((fun x : ℝ => ((x : ℝ) : ℂ)) '' Set.Ioi (0 : ℝ)).Infinite :=
    (Set.Ioi_infinite (0 : ℝ)).image hinj
  refine himg.mono ?_
  rintro z ⟨x, hx, rfl⟩
  exact ofReal_mem_rightHalfPlane hx

theorem rightHalfPlane_subset_slitPlane : rightHalfPlane ⊆ Complex.slitPlane :=
  fun _ hz => Or.inl hz

/-! ### Nonvanishing -/

theorem div_powerZero_ne_one_of_re_pos {z : ℂ} (hz : 0 < z.re) (s : ℝ) (n : ℕ) :
    z / powerZero s n ≠ 1 := by
  intro hcon
  rw [div_eq_one_iff_eq (powerZero_ne_zero s n)] at hcon
  have hre := congrArg Complex.re hcon
  rw [powerZero] at hre
  simp only [Complex.neg_re, Complex.ofReal_re] at hre
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ s := Real.rpow_pos_of_pos (by positivity) s
  linarith

theorem primaryFactor_div_powerZero_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (s : ℝ) (n : ℕ) :
    primaryFactor (powerGenus s) (z / powerZero s n) ≠ 0 := by
  rw [primaryFactor]
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  exact sub_ne_zero.mpr (Ne.symm (div_powerZero_ne_one_of_re_pos hz s n))

/-- **The power canonical product does not vanish on the right half-plane.** -/
theorem powerCanonicalProduct_ne_zero_of_re_pos (hs : 0 < s) {z : ℂ} (hz : 0 < z.re) :
    powerCanonicalProduct s z ≠ 0 := by
  have hsum : Summable fun n : ℕ =>
      ‖primaryFactor (powerGenus s) (z / powerZero s n) - 1‖ :=
    canonicalProduct_sub_one_norm_summable (powerGenus s) (powerZero s) (powerZero_ne_zero s)
      (powerZero_summable hs) z
  have hne : ∀ n : ℕ,
      1 + (primaryFactor (powerGenus s) (z / powerZero s n) - 1) ≠ 0 := by
    intro n
    rw [show (1 : ℂ) + (primaryFactor (powerGenus s) (z / powerZero s n) - 1)
      = primaryFactor (powerGenus s) (z / powerZero s n) by ring]
    exact primaryFactor_div_powerZero_ne_zero_of_re_pos hz s n
  have hprod := tprod_one_add_ne_zero_of_summable hne hsum
  have hshape : (fun n : ℕ => 1 + (primaryFactor (powerGenus s) (z / powerZero s n) - 1))
      = fun n : ℕ => primaryFactor (powerGenus s) (z / powerZero s n) := by
    funext n
    ring
  rw [hshape] at hprod
  exact hprod

end HTGeometry
