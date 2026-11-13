import GaloisForLFunctions.GaloisTheoryOfZeros.AZeroFollowedThroughSimpleZerosIsMovedByTheForwardMonodromy

/-!
# A zero alone in a moving region is followed through simple zeros

Along a path `γ` of times let `{z | d(s, z) ≤ 0}` be a bounded region of the fibre over `γ(s)`,
with `d` continuous. Suppose that for every `s`

* no zero of `H_{γ(s)}` lies on the edge `d(s, z) = 0`,
* the region contains at most one zero, and
* the zeros of the region are simple.

Then a zero in the region at `s = 0` is followed by a continuous family of zeros that stays in the
region (`exists_isZeroLift_of_alone`), and it is joined through simple zeros to the zero of the
region at `s = 1` (`exists_simplyJoined_of_alone`). The path may cross branch times: the collisions
happen outside the region. Only estimates at fixed times enter.

Proof. The set of parameters whose region contains a zero is closed (the zeros of the regions form
a compact set) and open (a simple zero persists, and stays off the edge). The zero of the region
is then a function of `s`; near every parameter it is the chart of a simple zero, so it is
continuous.
-/

open Complex Filter Topology Set Metric
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

variable {γ : ℝ → ℂ} {d : ℝ → ℂ → ℝ}

/-- **A simple zero inside the region persists.** Near a parameter `s₀` whose region contains the
simple zero `z₁` off the edge, a continuous family of zeros through `z₁` stays inside the
regions. -/
theorem exists_local_family_of_simple (hγ : ContinuousOn γ (Icc 0 1))
    (hd : ContinuousOn (fun p : ℝ × ℂ => d p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) {z₁ : ℂ} (hz : complexHeat (γ s₀) z₁ = 0) (hlt : d s₀ z₁ < 0)
    (hsimple : deriv (complexHeat (γ s₀)) z₁ ≠ 0) :
    ∃ ζ : ℂ → ℂ, ζ (γ s₀) = z₁ ∧ ContinuousWithinAt (fun s => ζ (γ s)) (Icc 0 1) s₀ ∧
      ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] s₀, complexHeat (γ s) (ζ (γ s)) = 0 ∧ d s (ζ (γ s)) < 0 := by
  obtain ⟨W, hWo, hτW, ρ, -, ζ, hζc, hζ0, hchart⟩ := exists_simple_zero_chart hz hsimple
  have hγs₀ : ContinuousWithinAt γ (Icc 0 1) s₀ := hγ s₀ hs₀
  have hζat : ContinuousAt ζ (γ s₀) := hζc.continuousAt (hWo.mem_nhds hτW)
  have hcomp : ContinuousWithinAt (fun s => ζ (γ s)) (Icc 0 1) s₀ :=
    hζat.comp_continuousWithinAt hγs₀
  have hpair : ContinuousWithinAt (fun s : ℝ => (s, ζ (γ s))) (Icc 0 1) s₀ :=
    continuousWithinAt_id.prodMk hcomp
  have hdat : ContinuousWithinAt (fun p : ℝ × ℂ => d p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ)
      (s₀, ζ (γ s₀)) := hd _ ⟨hs₀, mem_univ _⟩
  have hdcomp : ContinuousWithinAt (fun s : ℝ => d s (ζ (γ s))) (Icc 0 1) s₀ :=
    ContinuousWithinAt.comp (g := fun p : ℝ × ℂ => d p.1 p.2) (f := fun s : ℝ => (s, ζ (γ s)))
      hdat hpair fun s hs => ⟨hs, mem_univ _⟩
  have hd0 : d s₀ (ζ (γ s₀)) < 0 := by rwa [hζ0]
  refine ⟨ζ, hζ0, hcomp, ?_⟩
  filter_upwards [hγs₀.eventually (hWo.mem_nhds hτW), hdcomp.eventually (eventually_lt_nhds hd0)]
    with s hsW hsd
  exact ⟨(hchart _ hsW).2.1, hsd⟩

/-- The parameters whose region contains a zero form a closed set: the zeros of the regions form
a compact set of the plane of parameters and places. -/
theorem isClosed_setOf_exists_zero_inter_Icc {M : ℝ} (hγ : ContinuousOn γ (Icc 0 1))
    (hd : ContinuousOn (fun p : ℝ × ℂ => d p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, d s z ≤ 0 → ‖z‖ ≤ M) :
    IsClosed ({s | ∃ z, complexHeat (γ s) z = 0 ∧ d s z ≤ 0} ∩ Icc (0 : ℝ) 1) := by
  have hT : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) M) :=
    isCompact_Icc.prod (isCompact_closedBall 0 M)
  have hpairc : ContinuousOn (fun p : ℝ × ℂ => (γ p.1, p.2))
      (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) M) :=
    ContinuousOn.prodMk (hγ.comp continuousOn_fst fun p hp => hp.1) continuousOn_snd
  have hf₁ : ContinuousOn (fun p : ℝ × ℂ => complexHeat (γ p.1) p.2)
      (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) M) :=
    Continuous.comp_continuousOn (g := fun q : ℂ × ℂ => complexHeat q.1 q.2)
      (f := fun p : ℝ × ℂ => (γ p.1, p.2)) continuous_complexHeat hpairc
  have hf₂ : ContinuousOn (fun p : ℝ × ℂ => d p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) M) :=
    hd.mono (prod_mono subset_rfl (subset_univ _))
  have hc₁ : IsClosed (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) M ∩
      (fun p : ℝ × ℂ => complexHeat (γ p.1) p.2) ⁻¹' {0}) :=
    hf₁.preimage_isClosed_of_isClosed hT.isClosed isClosed_singleton
  have hc₂ : IsClosed (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) M ∩
      (fun p : ℝ × ℂ => d p.1 p.2) ⁻¹' Iic 0) :=
    hf₂.preimage_isClosed_of_isClosed hT.isClosed isClosed_Iic
  have hK := hT.of_isClosed_subset (hc₁.inter hc₂) fun p hp => hp.1.1
  have himg : {s | ∃ z, complexHeat (γ s) z = 0 ∧ d s z ≤ 0} ∩ Icc (0 : ℝ) 1 =
      Prod.fst '' ((Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) M ∩
        (fun p : ℝ × ℂ => complexHeat (γ p.1) p.2) ⁻¹' {0}) ∩
        (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) M ∩ (fun p : ℝ × ℂ => d p.1 p.2) ⁻¹' Iic 0)) := by
    ext s
    constructor
    · rintro ⟨⟨z, hz, hdz⟩, hs⟩
      have hzM : z ∈ closedBall (0 : ℂ) M := mem_closedBall_zero_iff.mpr (hM s hs z hdz)
      exact ⟨(s, z), ⟨⟨⟨hs, hzM⟩, hz⟩, ⟨⟨hs, hzM⟩, hdz⟩⟩, rfl⟩
    · rintro ⟨p, ⟨⟨hpT, hpz⟩, ⟨-, hpd⟩⟩, rfl⟩
      exact ⟨⟨p.2, hpz, hpd⟩, hpT.1⟩
  rw [himg]
  exact (hK.image continuous_fst).isClosed

/-- Every region contains a zero if the first one does. -/
theorem exists_zero_of_alone {M : ℝ} (hγ : ContinuousOn γ (Icc 0 1))
    (hd : ContinuousOn (fun p : ℝ × ℂ => d p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, d s z ≤ 0 → ‖z‖ ≤ M)
    (hedge : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, complexHeat (γ s) z = 0 → d s z ≤ 0 → d s z < 0)
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, complexHeat (γ s) z = 0 → d s z ≤ 0 →
      deriv (complexHeat (γ s)) z ≠ 0)
    {z₀ : ℂ} (h0 : complexHeat (γ 0) z₀ = 0) (hd0 : d 0 z₀ ≤ 0) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∃ z, complexHeat (γ s) z = 0 ∧ d s z ≤ 0 := by
  have hsub : Icc (0 : ℝ) 1 ⊆ {s | ∃ z, complexHeat (γ s) z = 0 ∧ d s z ≤ 0} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin
      (isClosed_setOf_exists_zero_inter_Icc hγ hd hM) ⟨z₀, h0, hd0⟩ ?_
    rintro x ⟨⟨z, hz, hdz⟩, hx⟩
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
    obtain ⟨ζ, -, -, hev⟩ := exists_local_family_of_simple hγ hd hxI hz
      (hedge x hxI z hz hdz) (hsimple x hxI z hz hdz)
    have hev' : ∀ᶠ s in 𝓝[>] x, complexHeat (γ s) (ζ (γ s)) = 0 ∧ d s (ζ (γ s)) < 0 := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hx.2]
      exact hev.filter_mono (nhdsWithin_mono _ fun y hy => ⟨hx.1.trans hy.1.le, hy.2.le⟩)
    filter_upwards [hev'] with s hs
    exact ⟨ζ (γ s), hs.1, hs.2.le⟩
  exact fun s hs => hsub hs

/-- **The zero of the region as a continuous family.** If along `γ` the bounded regions
`d(s, ·) ≤ 0` have no zero on the edge, at most one zero, and only simple zeros, then a zero of
the region at `s = 0` is followed by a continuous family of simple zeros inside the regions. -/
theorem exists_isZeroLift_of_alone {M : ℝ} (hγ : ContinuousOn γ (Icc 0 1))
    (hd : ContinuousOn (fun p : ℝ × ℂ => d p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, d s z ≤ 0 → ‖z‖ ≤ M)
    (hedge : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, complexHeat (γ s) z = 0 → d s z ≤ 0 → d s z < 0)
    (huniq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z z', complexHeat (γ s) z = 0 → d s z ≤ 0 →
      complexHeat (γ s) z' = 0 → d s z' ≤ 0 → z = z')
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, complexHeat (γ s) z = 0 → d s z ≤ 0 →
      deriv (complexHeat (γ s)) z ≠ 0)
    {z₀ : ℂ} (h0 : complexHeat (γ 0) z₀ = 0) (hd0 : d 0 z₀ ≤ 0) :
    ∃ w : ℝ → ℂ, IsZeroLift γ 1 w ∧ w 0 = z₀ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, d s (w s) < 0 ∧ deriv (complexHeat (γ s)) (w s) ≠ 0 := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  choose! w hw using exists_zero_of_alone hγ hd hM hedge hsimple h0 hd0
  have hw0 : w 0 = z₀ := huniq 0 h01 _ _ (hw 0 h01).1 (hw 0 h01).2 h0 hd0
  refine ⟨w, ⟨fun s₀ hs₀ => ?_, fun s hs => (hw s hs).1⟩, hw0, fun s hs =>
    ⟨hedge s hs _ (hw s hs).1 (hw s hs).2, hsimple s hs _ (hw s hs).1 (hw s hs).2⟩⟩
  -- near `s₀` the zero of the region is the chart of the simple zero `w s₀`
  obtain ⟨ζ, hζ0, hζc, hev⟩ := exists_local_family_of_simple hγ hd hs₀ (hw s₀ hs₀).1
    (hedge s₀ hs₀ _ (hw s₀ hs₀).1 (hw s₀ hs₀).2) (hsimple s₀ hs₀ _ (hw s₀ hs₀).1 (hw s₀ hs₀).2)
  refine hζc.congr_of_eventuallyEq ?_ hζ0.symm
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hsI
  exact huniq s hsI _ _ (hw s hsI).1 (hw s hsI).2 hs.1 hs.2.le

/-- **A zero alone in a moving region is joined through simple zeros to the zero of the last
region.** -/
theorem exists_simplyJoined_of_alone {M : ℝ} (hγ : ContinuousOn γ (Icc 0 1))
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re)
    (hd : ContinuousOn (fun p : ℝ × ℂ => d p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ univ))
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, d s z ≤ 0 → ‖z‖ ≤ M)
    (hedge : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, complexHeat (γ s) z = 0 → d s z ≤ 0 → d s z < 0)
    (huniq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z z', complexHeat (γ s) z = 0 → d s z ≤ 0 →
      complexHeat (γ s) z' = 0 → d s z' ≤ 0 → z = z')
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, complexHeat (γ s) z = 0 → d s z ≤ 0 →
      deriv (complexHeat (γ s)) z ≠ 0)
    {z₀ : ℂ} (h0 : complexHeat (γ 0) z₀ = 0) (hd0 : d 0 z₀ ≤ 0) :
    ∃ z₁, SimplyJoined (γ 0) z₀ (γ 1) z₁ ∧ complexHeat (γ 1) z₁ = 0 ∧ d 1 z₁ < 0 := by
  obtain ⟨w, hw, hw0, hprop⟩ := exists_isZeroLift_of_alone hγ hd hM hedge huniq hsimple h0 hd0
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  exact ⟨w 1, ⟨γ, w, hγ, hpos, hw, fun s hs => (hprop s hs).2, rfl, rfl, hw0, rfl⟩,
    hw.zero 1 h11, (hprop 1 h11).1⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
