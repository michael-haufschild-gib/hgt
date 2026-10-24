import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipOfTheMoebiusReceiverKeepsItsObstructions

/-!
# The flip pair carries the obstructions of the even part

For every weight `c` with summable mean, the even flip differs from `c` by a convolution of the even
part `c_e(d) = c(2d)` (`d` odd):

  `c♭ = c + (δ₁ − 2δ₂) ⋆ c_e`  (`evenFlip_eq_add_dirichletConv`).

The kernel `δ₁ − 2δ₂` is not a unit; its Bohr transform `1 − √2 ω(2)` vanishes only on the
hypersurface `ω(2) = 1/√2`, which contains no half-plane point with `Re s < 1`
(`bohrEval_flipDefect_halfPlane_ne_zero`).  Hence, with the calculus of the hull:

* **The flip moves the hull only inside the even part's hull**
  (`obstructionHull_evenFlip_subset_union`): `hull(c♭) ⊆ hull(c) ∪ hull(c_e)`, and symmetrically.
* **Conservation** (`mem_obstructionHull_or_evenFlip`): every obstruction of `c_e` off the
  hypersurface is an obstruction of `c` or of `c♭`; on the strip `½ ≤ Re s < 1` the flip pair
  carries all of `hull(c_e)` (`halfPlane_mem_obstructionHull_or_evenFlip`).
* **Both members paid** (`obstructionHull_evenPart_subset_of_paid`): then every obstruction of the
  even part lies on `ω(2) = 1/√2`, so `c_e` has no strip obstruction.
* **One member paid** (`mem_obstructionHull_evenFlip_of_paid`): the flip of a paid weight is
  obstructed exactly at the even part's obstructions off the hypersurface — the parity barrier
  (Fermi weight paid, its flip not) is this exposure of `hull(c_e)`.
-/

open Finset ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-- The flip defect kernel `δ₁ − 2δ₂`. -/
abbrev flipDefect : ℕ → ℝ := twoPoint 1 (-2)

theorem summable_abs_evenPartWeight_div {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|) :
    Summable fun d : ℕ => |evenPartWeight c d / d| := by
  have h2 : Summable fun d : ℕ => |c (2 * d) / ((2 * d : ℕ) : ℝ)| :=
    hc.comp_injective (fun a b h => by omega)
  refine (h2.mul_left 2).of_nonneg_of_le (fun _ => abs_nonneg _) fun d => ?_
  unfold evenPartWeight
  split_ifs
  · rcases eq_or_ne d 0 with rfl | hd
    · simp
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    rw [Nat.cast_mul, Nat.cast_ofNat, abs_div, abs_div, abs_of_pos hd0,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * d)]
    field_simp
    rfl
  · simp

/-- **The flip as a defect**: `c♭ = c + (δ₁ − 2δ₂) ⋆ c_e`. -/
theorem evenFlip_eq_add_dirichletConv (c : ℕ → ℝ) :
    evenFlip c = fun d => c d + RHTower.dirichletConv flipDefect (evenPartWeight c) d := by
  funext d
  unfold evenFlip
  congr 1
  rcases eq_or_ne d 0 with rfl | hd
  · simp [localFactorWeight, evenPartWeight, dirichletConv_twoPoint_zero]
  rw [dirichletConv_twoPoint _ _ _ hd]
  simp only [localFactorWeight, one_mul]
  ring

/-- The even part of the flip is minus the even part. -/
theorem evenPartWeight_evenFlip (c : ℕ → ℝ) :
    evenPartWeight (evenFlip c) = fun d => -1 * evenPartWeight c d := by
  funext d
  unfold evenPartWeight
  split_ifs with hd
  · have h1 : ¬ (2 * d) % 2 = 1 := by omega
    have h2 : (2 * d / 2) % 2 = 1 := by rw [Nat.mul_div_cancel_left d two_pos]; exact hd
    rw [evenFlip_apply, if_neg h1, if_pos h2]; ring
  · ring

theorem summable_abs_evenFlip_div' {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|) :
    Summable fun d : ℕ => |evenFlip c d / d| := by
  rw [evenFlip_eq_add_dirichletConv]
  exact summable_abs_add_div hc (summable_abs_dirichletConv_div (criticalWiener_twoPoint 1 (-2))
    (summable_abs_evenPartWeight_div hc))

/-- **The flip moves the hull only inside the even part's hull.** -/
theorem obstructionHull_evenFlip_subset_union {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|) :
    obstructionHull (evenFlip c) (summable_abs_evenFlip_div' hc) ⊆
      obstructionHull c hc ∪ obstructionHull (evenPartWeight c) (summable_abs_evenPartWeight_div hc) := by
  have he := summable_abs_evenPartWeight_div hc
  have hk := summable_abs_dirichletConv_div (criticalWiener_twoPoint 1 (-2)) he
  rw [obstructionHull_congr (evenFlip_eq_add_dirichletConv c) _ (summable_abs_add_div hc hk)]
  refine (obstructionHull_add_subset hc hk).trans (Set.union_subset_union_right _ ?_)
  exact obstructionHull_conv_subset _ he (criticalWiener_twoPoint 1 (-2))

/-- The symmetric inclusion: `hull(c) ⊆ hull(c♭) ∪ hull(c_e)`. -/
theorem obstructionHull_subset_evenFlip_union {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|) :
    obstructionHull c hc ⊆
      obstructionHull (evenFlip c) (summable_abs_evenFlip_div' hc) ∪
        obstructionHull (evenPartWeight c) (summable_abs_evenPartWeight_div hc) := by
  have hc' := summable_abs_evenFlip_div' hc
  have h := obstructionHull_evenFlip_subset_union hc'
  rw [obstructionHull_congr (evenFlip_evenFlip c) _ hc,
    obstructionHull_congr (evenPartWeight_evenFlip c) _
      (summable_abs_smul_div (summable_abs_evenPartWeight_div hc) (-1)),
    obstructionHull_smul _ (by norm_num : (-1 : ℝ) ≠ 0)] at h
  exact h

/-- The Bohr transform of the flip defect, `1 − 2 ω(2)/√2`. -/
theorem bohrEval_flipDefect (ω : BohrPoint) :
    bohrEval (1 / 2) (toWiener _ (criticalWiener_twoPoint 1 (-2))).toFn ω =
      1 - 2 * ω.ω 2 / (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
  rw [bohrEval_toWiener_twoPoint]; push_cast; ring

/-- **Conservation**: an obstruction of the even part off the hypersurface `ω(2) = 1/√2` is an
obstruction of `c` or of its flip. -/
theorem mem_obstructionHull_or_evenFlip {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    {ω : BohrPoint}
    (hω : ω ∈ obstructionHull (evenPartWeight c) (summable_abs_evenPartWeight_div hc))
    (hne : bohrEval (1 / 2) (toWiener _ (criticalWiener_twoPoint 1 (-2))).toFn ω ≠ 0) :
    ω ∈ obstructionHull c hc ∨ ω ∈ obstructionHull (evenFlip c) (summable_abs_evenFlip_div' hc) := by
  have he := summable_abs_evenPartWeight_div hc
  have hk := summable_abs_dirichletConv_div (criticalWiener_twoPoint 1 (-2)) he
  have h1 := mem_obstructionHull_conv _ he (criticalWiener_twoPoint 1 (-2)) hω hne
  by_cases h : ω ∈ obstructionHull c hc
  · exact Or.inl h
  · right
    rw [obstructionHull_congr (evenFlip_eq_add_dirichletConv c) _ (summable_abs_add_div hc hk)]
    -- `ω` is in `hull(k₀ ⋆ c_e)` and not in `hull(c)`, so it survives in the sum.
    have h2 := mem_obstructionHull_add_of_not_mem hk hc h1 h
    rw [obstructionHull_congr (funext fun d => add_comm _ _) _ (summable_abs_add_div hc hk)] at h2
    exact h2

/-- **Both members paid**: every obstruction of the even part lies on the hypersurface. -/
theorem obstructionHull_evenPart_subset_of_paid {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (h : ReceiverBounded c) (h' : ReceiverBounded (evenFlip c)) {ω : BohrPoint}
    (hω : ω ∈ obstructionHull (evenPartWeight c) (summable_abs_evenPartWeight_div hc)) :
    bohrEval (1 / 2) (toWiener _ (criticalWiener_twoPoint 1 (-2))).toFn ω = 0 := by
  by_contra hne
  rcases mem_obstructionHull_or_evenFlip hc hω hne with h1 | h1
  · exact (obstructionHull_nonempty_iff c hc).1 ⟨ω, h1⟩ h
  · exact (obstructionHull_nonempty_iff _ _).1 ⟨ω, h1⟩ h'

/-- **One member paid**: the flip of a paid weight is obstructed at every obstruction of its even
part off the hypersurface, and nowhere else. -/
theorem mem_obstructionHull_evenFlip_of_paid {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (h : ReceiverBounded c) {ω : BohrPoint}
    (hω : ω ∈ obstructionHull (evenPartWeight c) (summable_abs_evenPartWeight_div hc))
    (hne : bohrEval (1 / 2) (toWiener _ (criticalWiener_twoPoint 1 (-2))).toFn ω ≠ 0) :
    ω ∈ obstructionHull (evenFlip c) (summable_abs_evenFlip_div' hc) :=
  (mem_obstructionHull_or_evenFlip hc hω hne).resolve_left fun h1 =>
    (obstructionHull_nonempty_iff c hc).1 ⟨ω, h1⟩ h

theorem obstructionHull_evenFlip_subset_of_paid {c : ℕ → ℝ}
    (hc : Summable fun d : ℕ => |c d / d|) (h : ReceiverBounded c) :
    obstructionHull (evenFlip c) (summable_abs_evenFlip_div' hc) ⊆
      obstructionHull (evenPartWeight c) (summable_abs_evenPartWeight_div hc) := fun ω hω =>
  ((obstructionHull_evenFlip_subset_union hc) hω).resolve_left fun h1 =>
    (obstructionHull_nonempty_iff c hc).1 ⟨ω, h1⟩ h

/-! ### The strip misses the hypersurface -/

/-- At a half-plane point with `Re s < 1`, `1 − √2 ω(2) = 1 − 2^{1−s} ≠ 0`. -/
theorem bohrEval_flipDefect_halfPlane_ne_zero {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) (hs1 : s.re < 1) :
    bohrEval (1 / 2) (toWiener _ (criticalWiener_twoPoint 1 (-2))).toFn
      (halfPlanePoint (1 / 2) s hs) ≠ 0 := by
  rw [bohrEval_flipDefect]
  have hω : (halfPlanePoint (1 / 2) s hs).ω 2 = (2 : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - s) := by
    simp [halfPlanePoint]
  rw [hω, sub_ne_zero]
  intro h
  have hn := congrArg norm h
  have hsq : (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; norm_num
  have e1 : ‖(2 : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - s)‖ = (2 : ℝ) ^ (1 / 2 - s.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (two_pos : (0 : ℝ) < 2) (((1 / 2 : ℝ) : ℂ) - s)
    simpa using this
  have e2 : ‖(2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ)‖ = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (two_pos : (0 : ℝ) < 2) (((1 / 2 : ℝ)) : ℂ)
    simpa using this
  rw [norm_one, norm_div, norm_mul, Complex.norm_ofNat, e1, e2] at hn
  -- `2 · 2^{½ − Re s} / 2^{½} = 2^{1 − Re s} > 1`.
  have h1 : (1 : ℝ) < 2 * (2 : ℝ) ^ (1 / 2 - s.re) / (2 : ℝ) ^ (1 / 2 : ℝ) := by
    have e : 2 * (2 : ℝ) ^ (1 / 2 - s.re) / (2 : ℝ) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 - s.re) := by
      rw [mul_div_assoc, ← Real.rpow_sub two_pos,
        show (1 / 2 - s.re - 1 / 2 : ℝ) = (1 - s.re) - 1 by ring, Real.rpow_sub two_pos,
        Real.rpow_one]
      field_simp
    rw [e]
    exact Real.one_lt_rpow one_lt_two (by linarith)
  linarith

/-- **On the strip the flip pair carries the even part's obstructions.** -/
theorem halfPlane_mem_obstructionHull_or_evenFlip {c : ℕ → ℝ}
    (hc : Summable fun d : ℕ => |c d / d|) {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) (hs1 : s.re < 1)
    (hω : halfPlanePoint (1 / 2) s hs ∈
      obstructionHull (evenPartWeight c) (summable_abs_evenPartWeight_div hc)) :
    halfPlanePoint (1 / 2) s hs ∈ obstructionHull c hc ∨
      halfPlanePoint (1 / 2) s hs ∈ obstructionHull (evenFlip c) (summable_abs_evenFlip_div' hc) :=
  mem_obstructionHull_or_evenFlip hc hω (bohrEval_flipDefect_halfPlane_ne_zero hs hs1)

end

end GaloisForLFunctions.ArithmeticOrientationTheory
