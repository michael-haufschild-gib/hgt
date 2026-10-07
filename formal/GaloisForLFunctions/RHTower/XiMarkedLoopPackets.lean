import GaloisForLFunctions.RHTower.XiMarkedSourceSpace

/-!
# Actual Xi source loops realizing finite packets in one marked coordinate

Every finite packet of zero-winding target loops lifts at a common source
basepoint. Its other marked coordinates are nullhomotopic. The common
basepoint is essential for the subsequent finite-quotient conjugation argument.
-/

open Set Topology unitInterval Metric
open GaloisForLFunctions.HTGeometry Pi1CMinusZero

namespace RHTower.XiMarkedMonodromy

/-- A finite zero-winding packet can be realized in one coordinate, with all others trivial. -/
theorem exists_marked_source_loop_packet {ι : Type*} [Finite ι]
    (A : Finset ℝ) (a : A) (R : ℝ) {base : Target}
    (p : ι → Path base base)
    (hp : ∀ i, Bottcher.wind (fun z : Target => (z : ℂ))
      continuous_subtype_val (fun z => z.2.1) (p i) = 0) :
    ∃ s : Source A, R < (s : ℂ).re ∧
      ∃ hs : coordinate A a s = base,
      ∃ l : ι → Path s s, ∀ i,
        (((l i).map (coordinate A a).continuous).cast hs.symm hs.symm = p i) ∧
        ∀ b : A, b ≠ a →
          ((l i).map (coordinate A b).continuous).Homotopic
            (Path.refl (coordinate A b s)) := by
  classical
  obtain ⟨M, hM, w0, hwM, hw0, L, hL⟩ := exists_bounded_closed_log_lift_packet_at_base
    (fun i => (p i).map targetToPunctured.continuous) hp
  obtain ⟨h, hhd, hh⟩ := exists_xi_tilt_exp_lift_ball_separated A a M R hM
  have h0 : w0 ∈ ball 0 M := by simpa using hwM
  have hLmem (i : ι) (t : I) : L i t ∈ ball 0 M := by
    simpa using (hL i t).1
  have hxi (w : ℂ) (hw : w ∈ ball 0 M) : xi (h w) ≠ 0 := by
    intro hz
    have he := (hh w hw).2.1
    rw [hz, zero_mul] at he
    exact Complex.exp_ne_zero w he.symm
  have hother (b : A) (hba : b ≠ a) (w : ℂ) (hw : w ∈ ball 0 M) :
      value b (h w) ≠ -1 := by
    intro he
    have hne := (hh w hw).2.2 b b.2 (fun hab => hba (Subtype.ext hab))
    change ‖value b (h w)‖ ≠ 1 at hne
    apply hne
    rw [he, norm_neg, norm_one]
  have hsource (w : ℂ) (hw : w ∈ ball 0 M) (he : Complex.exp w ≠ -1) :
      h w ∈ sourceSet A := by
    refine ⟨hxi w hw, fun b hb => ?_⟩
    by_cases hba : b = a
    · subst b
      change xi (h w) * Complex.exp (-(a : ℂ) * h w) ≠ -1
      rw [(hh w hw).2.1]
      exact he
    · exact hother ⟨b, hb⟩ (fun hab => hba (congrArg Subtype.val hab)) w hw
  let s : Source A := ⟨h w0, hsource w0 h0 (by rw [hw0]; exact base.2.2)⟩
  have hs : coordinate A a s = base := by
    apply Subtype.ext
    exact (hh w0 h0).2.1.trans hw0
  have hlexp (i : ι) (t : I) : Complex.exp (L i t) ≠ -1 := by
    rw [(hL i t).2]
    exact (p i t).2.2
  let l (i : ι) : Path s s :=
    { toFun := fun t => ⟨h (L i t), hsource (L i t) (hLmem i t) (hlexp i t)⟩
      continuous_toFun :=
        (hhd.continuousOn.comp_continuous (L i).continuous (hLmem i)).subtype_mk _
      source' := by apply Subtype.ext; change h (L i 0) = h w0; rw [(L i).source]
      target' := by apply Subtype.ext; change h (L i 1) = h w0; rw [(L i).target] }
  refine ⟨s, (hh w0 h0).1, hs, l, fun i => ⟨?_, fun b hba => ?_⟩⟩
  · apply Path.ext
    funext t
    apply Subtype.ext
    exact (hh (L i t) (hLmem i t)).2.1.trans (hL i t).2
  · let D := ball (0 : ℂ) M
    let z0 : D := ⟨w0, h0⟩
    let lp : Path z0 z0 :=
      { toFun := fun t => ⟨L i t, hLmem i t⟩
        continuous_toFun := (L i).continuous.subtype_mk _
        source' := Subtype.ext (L i).source
        target' := Subtype.ext (L i).target }
    let F : C(D, Target) :=
      ⟨fun w => ⟨value b (h w),
        mul_ne_zero (hxi w w.2) (Complex.exp_ne_zero _), hother b hba w w.2⟩,
        ((value_differentiable b).continuous.comp hhd.continuousOn.restrict).subtype_mk _⟩
    letI : ContractibleSpace D := (convex_ball (0 : ℂ) M).contractibleSpace ⟨w0, h0⟩
    have hnull := (SimplyConnectedSpace.paths_homotopic lp (Path.refl z0)).map F
    convert hnull using 1 <;> rfl

end RHTower.XiMarkedMonodromy
