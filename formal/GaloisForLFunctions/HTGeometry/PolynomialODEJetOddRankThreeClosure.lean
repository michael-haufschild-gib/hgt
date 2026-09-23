import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeClosure

/-!
# Odd rank-three theta seam closure

Exact elimination through the twelfth modular mass derivative gives the odd
rank-three reflected Hankel determinant. Its polynomial is strictly negative
on the proved self-dual source interval. All identities are symbolic ring proofs.
-/

open scoped BigOperators ContDiff
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 6000000

/-- Modular polynomial for the signed odd rank-three reflected seam. -/
def modularThetaReflectedTenthSeamPolynomial {K : Type*} [Field K] (X : K) : K :=
    (16275380625 / 512) +
    (-142861674375 / 512) * X ^ (1 : ℕ) +
    (47752328428875 / 65536) * X ^ (2 : ℕ) +
    (-202162197691125 / 262144) * X ^ (3 : ℕ) +
    (359654516607375 / 1048576) * X ^ (4 : ℕ) +
    (-312458771094525 / 4194304) * X ^ (5 : ℕ) +
    (277466964716925 / 16777216) * X ^ (6 : ℕ) +
    (-289890788929155 / 67108864) * X ^ (7 : ℕ) +
    (65149999997625 / 268435456) * X ^ (8 : ℕ) +
    (-5811676667055 / 1073741824) * X ^ (9 : ℕ) +
    (1347619807251 / 1073741824) * X ^ (10 : ℕ) +
    (-86414468409 / 4294967296) * X ^ (11 : ℕ) +
    (34486304985 / 17179869184) * X ^ (12 : ℕ) +
    (-4788287325 / 17179869184) * X ^ (13 : ℕ) +
    (-374144625 / 137438953472) * X ^ (14 : ℕ) +
    (64029375 / 549755813888) * X ^ (15 : ℕ)

/-- Exact twelfth-jet elimination for the odd rank-three reflection block. -/
theorem modularThetaReflectedTenthSeamJetElimination
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
    let f : ℕ → ℂ :=
      fun n => (h (n + 2) - (1 / 4 : ℂ) * h n) / 2
    signedEvenHankelThreeDetC
      (-2 * f 0 * f 2)
      (2 * f 0 * f 4 + 6 * f 2 ^ (2 : ℕ))
      (-2 * f 0 * f 6 - 30 * f 2 * f 4)
      (2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ (2 : ℕ))
      (-2 * f 0 * f 10 - 90 * f 2 * f 8 - 420 * f 4 * f 6) =
      M ^ (6 : ℕ) * modularThetaReflectedTenthSeamPolynomial (R ^ (2 : ℕ)) := by
  have step1 : h 1 = M*(0) ∧
      z 1 = ((-1 / 1)*R^(1 : ℕ)) ∧
      r 1 = (0) ∧
      p 1 = ((3 / 1) + (1 / 4)*R^(2 : ℕ)) := by
    as_aux_lemma =>
      have hh1 := hh 0
      have hz1 := hz 0
      have hr1 := hr 0
      have hp1 := hp 0
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0]
          at hh1 hz1 hr1 hp1
      ring_nf at hh1 hz1 hr1 hp1
      refine ⟨?_, ?_, ?_, ?_⟩
      · convert hh1 using 1; ring
      · convert hz1 using 1; ring
      · exact hr1
      · convert hp1 using 1; ring
  obtain ⟨hh1, hz1, hr1, hp1⟩ := step1
  have step2 : h 2 = M*((-1 / 2) + (1 / 8)*R^(2 : ℕ)) ∧
      z 2 = (0) ∧
      r 2 = ((-2 / 1)*R^(1 : ℕ) + (1 / 2)*R^(3 : ℕ)) ∧
      p 2 = (0) := by
    as_aux_lemma =>
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
  obtain ⟨hh2, hz2, hr2, hp2⟩ := step2
  have step3 : h 3 = M*(0) ∧
      z 3 = ((2 / 1)*R^(1 : ℕ) + (3 / 2)*R^(3 : ℕ)) ∧
      r 3 = (0) ∧
      p 3 = ((-6 / 1) + (-2 / 1)*R^(2 : ℕ) + (3 / 8)*R^(4 : ℕ)) := by
    as_aux_lemma =>
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
  obtain ⟨hh3, hz3, hr3, hp3⟩ := step3
  have step4 : h 4 = M*((7 / 4) + (-11 / 8)*R^(2 : ℕ) + (-1 / 64)*R^(4 : ℕ)) ∧
      z 4 = (0) ∧
      r 4 = ((16 / 1)*R^(1 : ℕ) + (-10 / 1)*R^(3 : ℕ) + (1 / 2)*R^(5 : ℕ)) ∧
      p 4 = (0) := by
    as_aux_lemma =>
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
  obtain ⟨hh4, hz4, hr4, hp4⟩ := step4
  have step5 : h 5 = M*(0) ∧
      z 5 = ((-16 / 1)*R^(1 : ℕ) + (-30 / 1)*R^(3 : ℕ) + (-13 / 2)*R^(5 : ℕ)) ∧
      r 5 = (0) ∧
      p 5 = ((48 / 1) + (34 / 1)*R^(2 : ℕ) + (-15 / 1)*R^(4 : ℕ) + (3 / 8)*R^(6 : ℕ)) := by
    as_aux_lemma =>
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
  obtain ⟨hh5, hz5, hr5, hp5⟩ := step5
  have step6 : h 6 = M*((-139 / 8) + (889 / 32)*R^(2 : ℕ) + (95 / 128)*R^(4 : ℕ) + (51 / 512)*R^(6 : ℕ)) ∧
      z 6 = (0) ∧
      r 6 = ((-272 / 1)*R^(1 : ℕ) + (308 / 1)*R^(3 : ℕ) + (-35 / 1)*R^(5 : ℕ) + (3 / 4)*R^(7 : ℕ)) ∧
      p 6 = (0) := by
    as_aux_lemma =>
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
  obtain ⟨hh6, hz6, hr6, hp6⟩ := step6
  have step7 : h 7 = M*(0) ∧
      z 7 = ((272 / 1)*R^(1 : ℕ) + (924 / 1)*R^(3 : ℕ) + (455 / 1)*R^(5 : ℕ) + (189 / 4)*R^(7 : ℕ)) ∧
      r 7 = (0) ∧
      p 7 = ((-816 / 1) + (-992 / 1)*R^(2 : ℕ) + (756 / 1)*R^(4 : ℕ) + (-42 / 1)*R^(6 : ℕ) + (39 / 16)*R^(8 : ℕ)) := by
    as_aux_lemma =>
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
  obtain ⟨hh7, hz7, hr7, hp7⟩ := step7
  have step8 : h 8 = M*((5473 / 16) + (-14677 / 16)*R^(2 : ℕ) + (-5397 / 128)*R^(4 : ℕ) + (-3213 / 256)*R^(6 : ℕ) + (849 / 4096)*R^(8 : ℕ)) ∧
      z 8 = (0) ∧
      r 8 = ((7936 / 1)*R^(1 : ℕ) + (-14080 / 1)*R^(3 : ℕ) + (2688 / 1)*R^(5 : ℕ) + (-126 / 1)*R^(7 : ℕ) + (9 / 2)*R^(9 : ℕ)) ∧
      p 8 = (0) := by
    as_aux_lemma =>
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
  obtain ⟨hh8, hz8, hr8, hp8⟩ := step8
  have step9 : h 9 = M*(0) ∧
      z 9 = ((-7936 / 1)*R^(1 : ℕ) + (-42240 / 1)*R^(3 : ℕ) + (-34944 / 1)*R^(5 : ℕ) + (-7938 / 1)*R^(7 : ℕ) + (-1017 / 2)*R^(9 : ℕ)) ∧
      r 9 = (0) ∧
      p 9 = ((23808 / 1) + (44224 / 1)*R^(2 : ℕ) + (-50880 / 1)*R^(4 : ℕ) + (4662 / 1)*R^(6 : ℕ) + (-585 / 1)*R^(8 : ℕ) + (27 / 8)*R^(10 : ℕ)) := by
    as_aux_lemma =>
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
  obtain ⟨hh9, hz9, hr9, hp9⟩ := step9
  have step10 : h 10 = M*((-357721 / 32) + (5771821 / 128)*R^(2 : ℕ) + (797555 / 256)*R^(4 : ℕ) + (1562589 / 1024)*R^(6 : ℕ) + (-445725 / 8192)*R^(8 : ℕ) + (-26199 / 32768)*R^(10 : ℕ)) ∧
      z 10 = (0) ∧
      r 10 = ((-353792 / 1)*R^(1 : ℕ) + (902528 / 1)*R^(3 : ℕ) + (-254320 / 1)*R^(5 : ℕ) + (19404 / 1)*R^(7 : ℕ) + (-1485 / 1)*R^(9 : ℕ) + (117 / 4)*R^(11 : ℕ)) ∧
      p 10 = (0) := by
    as_aux_lemma =>
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
  obtain ⟨hh10, hz10, hr10, hp10⟩ := step10
  have step11 : h 11 = M*(0) ∧
      z 11 = ((353792 / 1)*R^(1 : ℕ) + (2707584 / 1)*R^(3 : ℕ) + (3306160 / 1)*R^(5 : ℕ) + (1222452 / 1)*R^(7 : ℕ) + (167805 / 1)*R^(9 : ℕ) + (30591 / 4)*R^(11 : ℕ)) ∧
      r 11 = (0) ∧
      p 11 = ((-1061376 / 1) + (-2796032 / 1)*R^(2 : ℕ) + (4491696 / 1)*R^(4 : ℕ) + (-598224 / 1)*R^(6 : ℕ) + (120978 / 1)*R^(8 : ℕ) + (-1485 / 1)*R^(10 : ℕ) + (1341 / 16)*R^(12 : ℕ)) := by
    as_aux_lemma =>
      have hh11 := hh 10
      have hz11 := hz 10
      have hr11 := hr 10
      have hp11 := hp 10
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
        hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5,
        hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8,
        hh9, hz9, hr9, hp9, hh10, hz10, hr10, hp10]
          at hh11 hz11 hr11 hp11
      ring_nf at hh11 hz11 hr11 hp11
      refine ⟨?_, ?_, ?_, ?_⟩
      · convert hh11 using 1; ring
      · convert hz11 using 1; ring
      · exact hr11
      · convert hp11 using 1; ring
  obtain ⟨hh11, hz11, hr11, hp11⟩ := step11
  have step12 : h 12 = M*((34988647 / 64) + (-395756081 / 128)*R^(2 : ℕ) + (-304210511 / 1024)*R^(4 : ℕ) + (-216096639 / 1024)*R^(6 : ℕ) + (198388377 / 16384)*R^(8 : ℕ) + (12392127 / 32768)*R^(10 : ℕ) + (1341999 / 262144)*R^(12 : ℕ)) := by
    as_aux_lemma =>
      have hh12 := hh 11
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
        hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5,
        hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8,
        hh9, hz9, hr9, hp9, hh10, hz10, hr10, hp10, hh11, hz11, hr11, hp11]
          at hh12
      ring_nf at hh12
      convert hh12 using 1; ring
  have hh12 := step12
  let f : ℕ → ℂ := fun n => (h (n+2)-(1/4:ℂ)*h n)/2
  let p0 (X : ℂ) : ℂ := (45 / 64) + (-165 / 256)*X^(1 : ℕ) + (21 / 256)*X^(2 : ℕ) + (1 / 1024)*X^(3 : ℕ)
  have he0 : -2 * f 0 * f 2 = M^(2 : ℕ)*p0 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4]
    dsimp [p0]
    ring
  let p1 (X : ℂ) : ℂ := (765 / 64) + (-2505 / 128)*X^(1 : ℕ) + (4461 / 1024)*X^(2 : ℕ) + (77 / 1024)*X^(3 : ℕ) + (27 / 4096)*X^(4 : ℕ)
  have he1 : 2 * f 0 * f 4 + 6 * f 2 ^ (2 : ℕ) = M^(2 : ℕ)*p1 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4, hh6]
    dsimp [p1]
    ring
  let p2 (X : ℂ) : ℂ := (24345 / 64) + (-243615 / 256)*X^(1 : ℕ) + (333759 / 1024)*X^(2 : ℕ) + (31519 / 4096)*X^(3 : ℕ) + (8199 / 4096)*X^(4 : ℕ) + (-21 / 16384)*X^(5 : ℕ)
  have he2 : -2 * f 0 * f 6 - 30 * f 2 * f 4 = M^(2 : ℕ)*p2 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4, hh6, hh8]
    dsimp [p2]
    ring
  let p3 (X : ℂ) : ℂ := (1207665 / 64) + (-2122095 / 32)*X^(1 : ℕ) + (16407993 / 512)*X^(2 : ℕ) + (1024127 / 1024)*X^(3 : ℕ) + (7963857 / 16384)*X^(4 : ℕ) + (-30027 / 16384)*X^(5 : ℕ) + (5133 / 65536)*X^(6 : ℕ)
  have he3 : 2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ (2 : ℕ) = M^(2 : ℕ)*p3 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4, hh6, hh8, hh10]
    dsimp [p3]
    ring
  let p4 (X : ℂ) : ℂ := (85066245 / 64) + (-1591823865 / 256)*X^(1 : ℕ) + (2049802467 / 512)*X^(2 : ℕ) + (327670217 / 2048)*X^(3 : ℕ) + (1966854177 / 16384)*X^(4 : ℕ) + (-62366877 / 65536)*X^(5 : ℕ) + (3218985 / 65536)*X^(6 : ℕ) + (-725859 / 262144)*X^(7 : ℕ)
  have he4 : -2 * f 0 * f 10 - 90 * f 2 * f 8 - 420 * f 4 * f 6 = M^(2 : ℕ)*p4 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4, hh6, hh8, hh10, hh12]
    dsimp [p4]
    ring
  change signedEvenHankelThreeDetC (-2 * f 0 * f 2) (2 * f 0 * f 4 + 6 * f 2 ^ (2 : ℕ)) (-2 * f 0 * f 6 - 30 * f 2 * f 4) (2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ (2 : ℕ)) (-2 * f 0 * f 10 - 90 * f 2 * f 8 - 420 * f 4 * f 6) = _
  rw [he0,he1,he2,he3,he4]
  have hscale (a b c d e : ℂ) :
      signedEvenHankelThreeDetC (M^(2 : ℕ)*a) (M^(2 : ℕ)*b) (M^(2 : ℕ)*c) (M^(2 : ℕ)*d) (M^(2 : ℕ)*e) =
      M^(6 : ℕ)*signedEvenHankelThreeDetC a b c d e := by
    unfold signedEvenHankelThreeDetC
    ring
  rw [hscale]
  congr 1
  have hp (X : ℂ) : signedEvenHankelThreeDetC (p0 X) (p1 X) (p2 X) (p3 X) (p4 X) =
      modularThetaReflectedTenthSeamPolynomial X := by
    dsimp [p0,p1,p2,p3,p4,signedEvenHankelThreeDetC,modularThetaReflectedTenthSeamPolynomial]
    ring
  exact hp (R^(2 : ℕ))


/-- The analytic modular ODE supplies every jet premise in the elimination. -/
theorem modularThetaReflectedTenthSeamClosure_of_ode
    (M R : ℂ) (h z r p : ℝ → ℂ)
    (hhc : ContDiff ℝ ∞ h) (hzc : ContDiff ℝ ∞ z)
    (hrc : ContDiff ℝ ∞ r) (hpc : ContDiff ℝ ∞ p)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh' : ∀ x, deriv h x =
      -(1 / 6 : ℂ) * (h x * (p x + r x * z x)))
    (hz' : ∀ x, deriv z x =
      -(r x * (1 - z x * z x)))
    (hr' : ∀ x, deriv r x =
      -(2 / 3 : ℂ) * (r x * (p x + r x * z x)))
    (hp' : ∀ x, deriv p x =
      3 - (1 / 3 : ℂ) * (p x * p x) +
        (1 / 12 : ℂ) * ((r x * r x) * (3 + z x * z x))) :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) h 0 -
        (1 / 4 : ℂ) * iteratedDeriv n h 0) / 2
    signedEvenHankelThreeDetC
      (-2 * f 0 * f 2)
      (2 * f 0 * f 4 + 6 * f 2 ^ (2 : ℕ))
      (-2 * f 0 * f 6 - 30 * f 2 * f 4)
      (2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ (2 : ℕ))
      (-2 * f 0 * f 10 - 90 * f 2 * f 8 - 420 * f 4 * f 6) =
      M ^ (6 : ℕ) * modularThetaReflectedTenthSeamPolynomial (R ^ (2 : ℕ)) := by
  let jh : ℕ → ℂ := fun n => iteratedDeriv n h 0
  let jz : ℕ → ℂ := fun n => iteratedDeriv n z 0
  let jr : ℕ → ℂ := fun n => iteratedDeriv n r 0
  let jp : ℕ → ℂ := fun n => iteratedDeriv n p 0
  have hunit (n : ℕ) :
      iteratedDeriv n (fun _ : ℝ => (1 : ℂ)) 0 =
        scalarJetUnit n := by
    cases n <;> simp [scalarJetUnit, iteratedDeriv_const]
  have hconst3 (n : ℕ) :
      iteratedDeriv n (fun _ : ℝ => (3 : ℂ)) 0 =
        3 * scalarJetUnit n := by
    cases n <;> simp [scalarJetUnit, iteratedDeriv_const]
  have hmul (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (n : ℕ) :
      iteratedDeriv n (f * g) 0 =
        scalarJetConvolution
          (fun k => iteratedDeriv k f 0)
          (fun k => iteratedDeriv k g 0) n := by
    exact iteratedDeriv_mul
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have hadd (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (n : ℕ) :
      iteratedDeriv n (f + g) 0 =
        iteratedDeriv n f 0 + iteratedDeriv n g 0 := by
    exact iteratedDeriv_add
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have hsub (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (n : ℕ) :
      iteratedDeriv n (f - g) 0 =
        iteratedDeriv n f 0 - iteratedDeriv n g 0 := by
    exact iteratedDeriv_sub
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have jh0 : jh 0 = M := by simpa [jh] using hh0
  have jz0 : jz 0 = 0 := by simpa [jz] using hz0
  have jr0 : jr 0 = R := by simpa [jr] using hr0
  have jp0 : jp 0 = 0 := by simpa [jp] using hp0
  have jhrec (n : ℕ) :
      jh (n + 1) =
        -(1 / 6 : ℂ) *
          scalarJetConvolution jh
            (fun k => jp k + scalarJetConvolution jr jz k) n := by
    simp only [jh, jp, jr, jz]
    rw [iteratedDeriv_succ']
    have heq : deriv h = fun x =>
        -(1 / 6 : ℂ) * (h x * (p x + r x * z x)) :=
      funext hh'
    rw [heq]
    rw [iteratedDeriv_const_mul (-(1 / 6 : ℂ))
      ((hhc.mul (hpc.add (hrc.mul hzc))).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change -(1 / 6 : ℂ) *
        iteratedDeriv n (h * (p + r * z)) 0 = _
    rw [hmul h (p + r * z) hhc
      (hpc.add (hrc.mul hzc)) n]
    unfold scalarJetConvolution
    apply congrArg (fun q : ℂ => -(1 / 6 : ℂ) * q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only
    rw [hadd p (r * z) hpc (hrc.mul hzc)]
    rw [hmul r z hrc hzc]
    rfl
  have jzrec (n : ℕ) :
      jz (n + 1) =
        -scalarJetConvolution jr
          (fun k => scalarJetUnit k -
            scalarJetConvolution jz jz k) n := by
    simp only [jz, jr]
    rw [iteratedDeriv_succ']
    have heq : deriv z = fun x =>
        (-1 : ℂ) * (r x * (1 - z x * z x)) := by
      funext x
      rw [hz']
      ring
    rw [heq]
    rw [iteratedDeriv_const_mul (-1 : ℂ)
      ((hrc.mul (contDiff_const.sub (hzc.mul hzc))).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change (-1 : ℂ) *
        iteratedDeriv n (r * ((fun _ : ℝ => (1 : ℂ)) - z * z)) 0 = _
    rw [hmul r ((fun _ : ℝ => (1 : ℂ)) - z * z) hrc
      (contDiff_const.sub (hzc.mul hzc)) n]
    unfold scalarJetConvolution
    rw [neg_one_mul]
    apply congrArg (fun q : ℂ => -q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only
    rw [hsub (fun _ : ℝ => (1 : ℂ)) (z * z)
      contDiff_const (hzc.mul hzc), hunit]
    rw [hmul z z hzc hzc]
    rfl
  have jrrec (n : ℕ) :
      jr (n + 1) =
        -(2 / 3 : ℂ) *
          scalarJetConvolution jr
            (fun k => jp k + scalarJetConvolution jr jz k) n := by
    simp only [jr, jp, jz]
    rw [iteratedDeriv_succ']
    have heq : deriv r = fun x =>
        -(2 / 3 : ℂ) * (r x * (p x + r x * z x)) :=
      funext hr'
    rw [heq]
    rw [iteratedDeriv_const_mul (-(2 / 3 : ℂ))
      ((hrc.mul (hpc.add (hrc.mul hzc))).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change -(2 / 3 : ℂ) *
        iteratedDeriv n (r * (p + r * z)) 0 = _
    rw [hmul r (p + r * z) hrc
      (hpc.add (hrc.mul hzc)) n]
    unfold scalarJetConvolution
    apply congrArg (fun q : ℂ => -(2 / 3 : ℂ) * q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only
    rw [hadd p (r * z) hpc (hrc.mul hzc)]
    rw [hmul r z hrc hzc]
    rfl
  have jprec (n : ℕ) :
      jp (n + 1) =
        3 * scalarJetUnit n -
          (1 / 3 : ℂ) * scalarJetConvolution jp jp n +
          (1 / 12 : ℂ) *
            scalarJetConvolution (scalarJetConvolution jr jr)
              (fun k => 3 * scalarJetUnit k +
                scalarJetConvolution jz jz k) n := by
    simp only [jp, jr, jz]
    rw [iteratedDeriv_succ']
    have heq : deriv p = fun x =>
        3 - (1 / 3 : ℂ) * (p x * p x) +
          (1 / 12 : ℂ) * ((r x * r x) * (3 + z x * z x)) :=
      funext hp'
    rw [heq]
    change iteratedDeriv n
        ((fun x : ℝ => (3 : ℂ) - (1 / 3 : ℂ) * (p x * p x)) +
          fun x : ℝ =>
            (1 / 12 : ℂ) * ((r x * r x) * (3 + z x * z x))) 0 = _
    rw [iteratedDeriv_add
      ((contDiff_const.sub
        (contDiff_const.mul (hpc.mul hpc))).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      ((contDiff_const.mul ((hrc.mul hrc).mul
        (contDiff_const.add (hzc.mul hzc)))).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change
      iteratedDeriv n
          ((fun _ : ℝ => (3 : ℂ)) -
            fun x => (1 / 3 : ℂ) * (p x * p x)) 0 +
        iteratedDeriv n
          (fun x => (1 / 12 : ℂ) *
            ((r x * r x) * (3 + z x * z x))) 0 = _
    rw [iteratedDeriv_sub contDiffAt_const
      ((contDiff_const.mul (hpc.mul hpc)).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    rw [hconst3]
    rw [iteratedDeriv_const_mul (1 / 3 : ℂ)
      ((hpc.mul hpc).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change
      3 * scalarJetUnit n -
          (1 / 3 : ℂ) * iteratedDeriv n (p * p) 0 +
        iteratedDeriv n
          (fun x => (1 / 12 : ℂ) *
            ((r x * r x) * (3 + z x * z x))) 0 = _
    rw [hmul p p hpc hpc]
    rw [iteratedDeriv_const_mul (1 / 12 : ℂ)
      (((hrc.mul hrc).mul
        (contDiff_const.add (hzc.mul hzc))).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change
      3 * scalarJetUnit n -
          (1 / 3 : ℂ) *
            scalarJetConvolution
              (fun k => iteratedDeriv k p 0)
              (fun k => iteratedDeriv k p 0) n +
        (1 / 12 : ℂ) *
          iteratedDeriv n
            ((r * r) * ((fun _ : ℝ => (3 : ℂ)) + z * z)) 0 = _
    rw [hmul (r * r) ((fun _ : ℝ => (3 : ℂ)) + z * z)
      (hrc.mul hrc) (contDiff_const.add (hzc.mul hzc)) n]
    unfold scalarJetConvolution
    apply congrArg (fun q : ℂ =>
      3 * scalarJetUnit n -
          (1 / 3 : ℂ) *
            scalarJetConvolution
              (fun k => iteratedDeriv k p 0)
              (fun k => iteratedDeriv k p 0) n +
        (1 / 12 : ℂ) * q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    · simp only
      rw [hmul r r hrc hrc]
      rfl
    · simp only
      rw [hadd (fun _ : ℝ => (3 : ℂ)) (z * z)
            contDiff_const (hzc.mul hzc),
          hconst3, hmul z z hzc hzc]
      rfl
  exact modularThetaReflectedTenthSeamJetElimination M R jh jz jr jp
    jh0 jz0 jr0 jp0 jhrec jzrec jrrec jprec


/-- The odd seam polynomial is strictly negative throughout the physical scale box. -/
theorem modularThetaReflectedTenthSeamPolynomial_neg
    {X : ℝ} (hlo : (191 / 10 : ℝ) ≤ X) (hhi : X ≤ 20) :
    modularThetaReflectedTenthSeamPolynomial X < 0 := by
  let y := X - (191 / 10 : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hy1 : y ≤ 1 := by dsimp [y]; linarith
  have hp (n : ℕ) : 0 ≤ 1 - y ^ n := sub_nonneg.mpr (pow_le_one₀ hy hy1)
  have hp10 := hp 10
  have hp11 := hp 11
  have hp12 := hp 12
  have hp13 := hp 13
  have hp14 := hp 14
  have hp15 := hp 15
  have hid : -modularThetaReflectedTenthSeamPolynomial X =
    (3080564923922620491692066740103039457303 / 879609302220800000000000) +
    (288928943152129489135184947353297944079 / 87960930222080000000000) * y ^ (1 : ℕ) +
    (11321713529114845042401117131584954431 / 8796093022208000000000) * y ^ (2 : ℕ) +
    (253119115555290587202283703900801943 / 879609302220800000000) * y ^ (3 : ℕ) +
    (3659802059631348335832242882094531 / 87960930222080000000) * y ^ (4 : ℕ) +
    (36394175284728826123552042590939 / 8796093022208000000) * y ^ (5 : ℕ) +
    (255841041175510266612905628123 / 879609302220800000) * y ^ (6 : ℕ) +
    (1270263926884626239933284947 / 87960930222080000) * y ^ (7 : ℕ) +
    (4263297908633393345054181 / 8796093022208000) * y ^ (8 : ℕ) +
    (8062147230190312679757 / 879609302220800) * y ^ (9 : ℕ) +
    (1437012024369451011 / 87960930222080) * (1 - y ^ (10 : ℕ)) +
    (59484862171607931 / 8796093022208) * (1 - y ^ (11 : ℕ)) +
    (930978403404795 / 4398046511104) * (1 - y ^ (12 : ℕ)) +
    (7596952502175 / 2199023255552) * (1 - y ^ (13 : ℕ)) +
    (33695674875 / 1099511627776) * (1 - y ^ (14 : ℕ)) +
    (64029375 / 549755813888) * (1 - y ^ (15 : ℕ)) := by
    dsimp [y, modularThetaReflectedTenthSeamPolynomial]
    ring
  have hpos : 0 < -modularThetaReflectedTenthSeamPolynomial X := by
    rw [hid]
    positivity
  linarith

end
end HTGeometry
