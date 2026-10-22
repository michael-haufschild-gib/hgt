import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthCenterModularPolynomial
import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeSeamRestriction
/-!
# Exact even modular mass jets for the growth center

Scalar modular ODE recurrences identify every even mass jet through ten.
Each recurrence step is checked separately at the default elaboration
limit; the final theorem supplies the exact source-jet polynomials.
-/
namespace RHTower.ThetaCuspDefect
open HTGeometry
open scoped BigOperators ContDiff
noncomputable section

private theorem centerMassStep1
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (_hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 1 = M*(0) ∧
      z 1 = ((-1 / 1)*R^(1 : ℕ)) ∧
      r 1 = (0) ∧
      p 1 = ((3 / 1) + (1 / 4)*R^(2 : ℕ)) := by
  have hh1 := hh 0
  have hz1 := hz 0
  have hr1 := hr 0
  have hp1 := hp 0
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    _hh0, hz0, hr0, hp0]
      at hh1 hz1 hr1 hp1
  ring_nf at hh1 hz1 hr1 hp1
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh1 using 1; ring
  · convert hz1 using 1; ring
  · exact hr1
  · convert hp1 using 1; ring

private theorem centerMassStep2
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 2 = M*((-1 / 2) + (1 / 8)*R^(2 : ℕ)) ∧
      z 2 = (0) ∧
      r 2 = ((-2 / 1)*R^(1 : ℕ) + (1 / 2)*R^(3 : ℕ)) ∧
      p 2 = (0) := by
  obtain ⟨hh1, hz1, hr1, hp1⟩ := centerMassStep1 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  have hh2 := hh 1
  have hz2 := hz 1
  have hr2 := hr 1
  have hp2 := hp 1
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1]
      at hh2 hz2 hr2 hp2
  ring_nf at hh2 hz2 hr2 hp2
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh2 using 1; ring
  · exact hz2
  · convert hr2 using 1; ring
  · exact hp2

private theorem centerMassStep3
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 3 = M*(0) ∧
      z 3 = ((2 / 1)*R^(1 : ℕ) + (3 / 2)*R^(3 : ℕ)) ∧
      r 3 = (0) ∧
      p 3 = ((-6 / 1) + (-2 / 1)*R^(2 : ℕ) + (3 / 8)*R^(4 : ℕ)) := by
  obtain ⟨hh1, hz1, hr1, hp1⟩ := centerMassStep1 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh2, hz2, hr2, hp2⟩ := centerMassStep2 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  have hh3 := hh 2
  have hz3 := hz 2
  have hr3 := hr 2
  have hp3 := hp 2
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2]
      at hh3 hz3 hr3 hp3
  ring_nf at hh3 hz3 hr3 hp3
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh3 using 1; ring
  · convert hz3 using 1; ring
  · exact hr3
  · convert hp3 using 1; ring

private theorem centerMassStep4
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 4 = M*((7 / 4) + (-11 / 8)*R^(2 : ℕ) + (-1 / 64)*R^(4 : ℕ)) ∧
      z 4 = (0) ∧
      r 4 = ((16 / 1)*R^(1 : ℕ) + (-10 / 1)*R^(3 : ℕ) + (1 / 2)*R^(5 : ℕ)) ∧
      p 4 = (0) := by
  obtain ⟨hh1, hz1, hr1, hp1⟩ := centerMassStep1 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh2, hz2, hr2, hp2⟩ := centerMassStep2 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh3, hz3, hr3, hp3⟩ := centerMassStep3 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  have hh4 := hh 3
  have hz4 := hz 3
  have hr4 := hr 3
  have hp4 := hp 3
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3]
      at hh4 hz4 hr4 hp4
  ring_nf at hh4 hz4 hr4 hp4
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh4 using 1; ring
  · exact hz4
  · convert hr4 using 1; ring
  · exact hp4

private theorem centerMassStep5
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 5 = M*(0) ∧
      z 5 = ((-16 / 1)*R^(1 : ℕ) + (-30 / 1)*R^(3 : ℕ) + (-13 / 2)*R^(5 : ℕ)) ∧
      r 5 = (0) ∧
      p 5 = ((48 / 1) + (34 / 1)*R^(2 : ℕ) + (-15 / 1)*R^(4 : ℕ) + (3 / 8)*R^(6 : ℕ)) := by
  obtain ⟨hh1, hz1, hr1, hp1⟩ := centerMassStep1 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh2, hz2, hr2, hp2⟩ := centerMassStep2 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh3, hz3, hr3, hp3⟩ := centerMassStep3 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh4, hz4, hr4, hp4⟩ := centerMassStep4 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  have hh5 := hh 4
  have hz5 := hz 4
  have hr5 := hr 4
  have hp5 := hp 4
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4]
      at hh5 hz5 hr5 hp5
  ring_nf at hh5 hz5 hr5 hp5
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh5 using 1; ring
  · convert hz5 using 1; ring
  · exact hr5
  · convert hp5 using 1; ring

private theorem centerMassStep6
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 6 = M*((-139 / 8) + (889 / 32)*R^(2 : ℕ) + (95 / 128)*R^(4 : ℕ) + (51 / 512)*R^(6 : ℕ)) ∧
      z 6 = (0) ∧
      r 6 = ((-272 / 1)*R^(1 : ℕ) + (308 / 1)*R^(3 : ℕ) + (-35 / 1)*R^(5 : ℕ) + (3 / 4)*R^(7 : ℕ)) ∧
      p 6 = (0) := by
  obtain ⟨hh1, hz1, hr1, hp1⟩ := centerMassStep1 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh2, hz2, hr2, hp2⟩ := centerMassStep2 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh3, hz3, hr3, hp3⟩ := centerMassStep3 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh4, hz4, hr4, hp4⟩ := centerMassStep4 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh5, hz5, hr5, hp5⟩ := centerMassStep5 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  have hh6 := hh 5
  have hz6 := hz 5
  have hr6 := hr 5
  have hp6 := hp 5
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5]
      at hh6 hz6 hr6 hp6
  ring_nf at hh6 hz6 hr6 hp6
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh6 using 1; ring
  · exact hz6
  · convert hr6 using 1; ring
  · exact hp6

private theorem centerMassStep7
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 7 = M*(0) ∧
      z 7 = ((272 / 1)*R^(1 : ℕ) + (924 / 1)*R^(3 : ℕ) + (455 / 1)*R^(5 : ℕ) + (189 / 4)*R^(7 : ℕ)) ∧
      r 7 = (0) ∧
      p 7 = ((-816 / 1) + (-992 / 1)*R^(2 : ℕ) + (756 / 1)*R^(4 : ℕ) + (-42 / 1)*R^(6 : ℕ) + (39 / 16)*R^(8 : ℕ)) := by
  obtain ⟨hh1, hz1, hr1, hp1⟩ := centerMassStep1 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh2, hz2, hr2, hp2⟩ := centerMassStep2 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh3, hz3, hr3, hp3⟩ := centerMassStep3 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh4, hz4, hr4, hp4⟩ := centerMassStep4 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh5, hz5, hr5, hp5⟩ := centerMassStep5 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh6, hz6, hr6, hp6⟩ := centerMassStep6 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  have hh7 := hh 6
  have hz7 := hz 6
  have hr7 := hr 6
  have hp7 := hp 6
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5,
    hh6, hz6, hr6, hp6]
      at hh7 hz7 hr7 hp7
  ring_nf at hh7 hz7 hr7 hp7
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh7 using 1; ring
  · convert hz7 using 1; ring
  · exact hr7
  · convert hp7 using 1; ring

private theorem centerMassStep8
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 8 = M*((5473 / 16) + (-14677 / 16)*R^(2 : ℕ) + (-5397 / 128)*R^(4 : ℕ) + (-3213 / 256)*R^(6 : ℕ) + (849 / 4096)*R^(8 : ℕ)) ∧
      z 8 = (0) ∧
      r 8 = ((7936 / 1)*R^(1 : ℕ) + (-14080 / 1)*R^(3 : ℕ) + (2688 / 1)*R^(5 : ℕ) + (-126 / 1)*R^(7 : ℕ) + (9 / 2)*R^(9 : ℕ)) ∧
      p 8 = (0) := by
  obtain ⟨hh1, hz1, hr1, hp1⟩ := centerMassStep1 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh2, hz2, hr2, hp2⟩ := centerMassStep2 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh3, hz3, hr3, hp3⟩ := centerMassStep3 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh4, hz4, hr4, hp4⟩ := centerMassStep4 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh5, hz5, hr5, hp5⟩ := centerMassStep5 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh6, hz6, hr6, hp6⟩ := centerMassStep6 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh7, hz7, hr7, hp7⟩ := centerMassStep7 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  have hh8 := hh 7
  have hz8 := hz 7
  have hr8 := hr 7
  have hp8 := hp 7
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5,
    hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7]
      at hh8 hz8 hr8 hp8
  ring_nf at hh8 hz8 hr8 hp8
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh8 using 1; ring
  · exact hz8
  · convert hr8 using 1; ring
  · exact hp8

private theorem centerMassStep9
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 9 = M*(0) ∧
      z 9 = ((-7936 / 1)*R^(1 : ℕ) + (-42240 / 1)*R^(3 : ℕ) + (-34944 / 1)*R^(5 : ℕ) + (-7938 / 1)*R^(7 : ℕ) + (-1017 / 2)*R^(9 : ℕ)) ∧
      r 9 = (0) ∧
      p 9 = ((23808 / 1) + (44224 / 1)*R^(2 : ℕ) + (-50880 / 1)*R^(4 : ℕ) + (4662 / 1)*R^(6 : ℕ) + (-585 / 1)*R^(8 : ℕ) + (27 / 8)*R^(10 : ℕ)) := by
  obtain ⟨hh1, hz1, hr1, hp1⟩ := centerMassStep1 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh2, hz2, hr2, hp2⟩ := centerMassStep2 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh3, hz3, hr3, hp3⟩ := centerMassStep3 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh4, hz4, hr4, hp4⟩ := centerMassStep4 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh5, hz5, hr5, hp5⟩ := centerMassStep5 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh6, hz6, hr6, hp6⟩ := centerMassStep6 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh7, hz7, hr7, hp7⟩ := centerMassStep7 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh8, hz8, hr8, hp8⟩ := centerMassStep8 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  have hh9 := hh 8
  have hz9 := hz 8
  have hr9 := hr 8
  have hp9 := hp 8
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5,
    hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8]
      at hh9 hz9 hr9 hp9
  ring_nf at hh9 hz9 hr9 hp9
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh9 using 1; ring
  · convert hz9 using 1; ring
  · exact hr9
  · convert hp9 using 1; ring

private theorem centerMassStep10
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
 h 10 = M*((-357721 / 32) + (5771821 / 128)*R^(2 : ℕ) + (797555 / 256)*R^(4 : ℕ) + (1562589 / 1024)*R^(6 : ℕ) + (-445725 / 8192)*R^(8 : ℕ) + (-26199 / 32768)*R^(10 : ℕ)) ∧
      z 10 = (0) ∧
      r 10 = ((-353792 / 1)*R^(1 : ℕ) + (902528 / 1)*R^(3 : ℕ) + (-254320 / 1)*R^(5 : ℕ) + (19404 / 1)*R^(7 : ℕ) + (-1485 / 1)*R^(9 : ℕ) + (117 / 4)*R^(11 : ℕ)) ∧
      p 10 = (0) := by
  obtain ⟨hh1, hz1, hr1, hp1⟩ := centerMassStep1 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh2, hz2, hr2, hp2⟩ := centerMassStep2 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh3, hz3, hr3, hp3⟩ := centerMassStep3 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh4, hz4, hr4, hp4⟩ := centerMassStep4 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh5, hz5, hr5, hp5⟩ := centerMassStep5 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh6, hz6, hr6, hp6⟩ := centerMassStep6 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh7, hz7, hr7, hp7⟩ := centerMassStep7 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh8, hz8, hr8, hp8⟩ := centerMassStep8 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  obtain ⟨hh9, hz9, hr9, hp9⟩ := centerMassStep9 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp
  have hh10 := hh 9
  have hz10 := hz 9
  have hr10 := hr 9
  have hp10 := hp 9
  norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
    hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5,
    hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8,
    hh9, hz9, hr9, hp9]
      at hh10 hz10 hr10 hp10
  ring_nf at hh10 hz10 hr10 hp10
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hh10 using 1; ring
  · exact hz10
  · convert hr10 using 1; ring
  · exact hp10

theorem centerMassJet_elimination
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
    ∀ j : ℕ, j ≤ 5 → h (2*j)=M*centerMassJet (R^2) (2*j) := by
  have hh2 := (centerMassStep2 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp).1
  have hh4 := (centerMassStep4 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp).1
  have hh6 := (centerMassStep6 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp).1
  have hh8 := (centerMassStep8 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp).1
  have hh10 := (centerMassStep10 M R h z r p hh0 hz0 hr0 hp0 hh hz hr hp).1
  intro j hj
  interval_cases j <;> norm_num only [Nat.reduceMul]
  · simpa only [centerMassJet,mul_one] using hh0
  · rw [hh2]; simp only [centerMassJet]; ring
  · rw [hh4]; simp only [centerMassJet]; ring
  · rw [hh6]; simp only [centerMassJet]; ring
  · rw [hh8]; simp only [centerMassJet]; ring
  · rw [hh10]; simp only [centerMassJet]; ring

end
end RHTower.ThetaCuspDefect
