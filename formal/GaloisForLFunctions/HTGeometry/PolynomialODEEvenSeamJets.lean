import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSeamRestriction

/-! # Exact even source jets through twelve at the algebraic modular seam -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 6000000

/-- Normalized source derivatives of orders zero through twelve at the seam. -/
def modularThetaEvenSeamSourcePolynomial {K : Type*} [Field K] (n : Fin 7) (X : K) : K :=
  match n.val with
  | 0 => (-3/8) + (1/16)*X^(1 : ℕ)
  | 1 => (15/16) + (-45/64)*X^(1 : ℕ) + (-1/128)*X^(2 : ℕ)
  | 2 => (-285/32) + (225/16)*X^(1 : ℕ) + (191/512)*X^(2 : ℕ) + (51/1024)*X^(3 : ℕ)
  | 3 => (11085/64) + (-118305/256)*X^(1 : ℕ) + (-21683/1024)*X^(2 : ℕ) + (-25755/4096)*X^(3 : ℕ) + (849/8192)*X^(4 : ℕ)
  | 4 => (-720915/128) + (5801175/256)*X^(1 : ℕ) + (1600507/1024)*X^(2 : ℕ) + (782901/1024)*X^(3 : ℕ) + (-892299/32768)*X^(4 : ℕ) + (-26199/65536)*X^(5 : ℕ)
  | 5 => (70335015/256) + (-1588796145/1024)*X^(1 : ℕ) + (-152504033/1024)*X^(2 : ℕ) + (-865949145/8192)*X^(3 : ℕ) + (397222479/65536)*X^(4 : ℕ) + (49594707/262144)*X^(5 : ℕ) + (1341999/524288)*X^(6 : ℕ)
  | _ => (-9603111885/512) + (72410457375/512)*X^(1 : ℕ) + (146977580081/8192)*X^(2 : ℕ) + (281792785791/16384)*X^(3 : ℕ) + (-183992803467/131072)*X^(4 : ℕ) + (-2279863179/32768)*X^(5 : ℕ) + (-4153486905/2097152)*X^(6 : ℕ) + (82018251/4194304)*X^(7 : ℕ)

/-- The full four-state modular recurrence gives every required even seam source jet exactly. -/
theorem eval_modularThetaODESourceJet_even_seam (R : ℂ) (k : Fin 7) :
    MvPolynomial.eval (modularThetaODESeamState R) (modularThetaODESourceJet (2*k.val)) =
      modularThetaEvenSeamSourcePolynomial k (R^(2 : ℕ)) := by
  let v := modularThetaODESeamState R
  let h := evalModularThetaODEFormalJet v .H
  let z := evalModularThetaODEFormalJet v .Z
  let r := evalModularThetaODEFormalJet v .R
  let p := evalModularThetaODEFormalJet v .P
  have hh0 : h 0 = 1 := by simp [h, v, modularThetaODESeamState]
  have hz0 : z 0 = 0 := by simp [z, v, modularThetaODESeamState]
  have hr0 : r 0 = R := by simp [r, v, modularThetaODESeamState]
  have hp0 : p 0 = 0 := by simp [p, v, modularThetaODESeamState]
  have hh (n : ℕ) : h (n+1) = -(1/6:ℂ)*scalarJetConvolution h
      (fun k => p k+scalarJetConvolution r z k) n :=
    evalModularThetaODEFormalJet_H_succ v n
  have hz (n : ℕ) : z (n+1) = -scalarJetConvolution r
      (fun k => scalarJetUnit k-scalarJetConvolution z z k) n :=
    evalModularThetaODEFormalJet_Z_succ v n
  have hr (n : ℕ) : r (n+1) = -(2/3:ℂ)*scalarJetConvolution r
      (fun k => p k+scalarJetConvolution r z k) n :=
    evalModularThetaODEFormalJet_R_succ v n
  have hp (n : ℕ) : p (n+1) = 3*scalarJetUnit n-(1/3:ℂ)*scalarJetConvolution p p n+
      (1/12:ℂ)*scalarJetConvolution (scalarJetConvolution r r)
        (fun k => 3*scalarJetUnit k+scalarJetConvolution z z k) n :=
    evalModularThetaODEFormalJet_P_succ v n
  have step1 : h 1 = 0 ∧
      z 1 = (-1)*R^(1 : ℕ) ∧
      r 1 = 0 ∧
      p 1 = (3) + (1/4)*R^(2 : ℕ) := by
    as_aux_lemma =>
      have hh1 := hh 0
      have hz1 := hz 0
      have hr1 := hr 0
      have hp1 := hp 0
      change h 1 = 0 ∧
        z 1 = (-1)*R^(1 : ℕ) ∧
        r 1 = 0 ∧
        p 1 = (3) + (1/4)*R^(2 : ℕ)
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0]
          at hh1 hz1 hr1 hp1
      ring_nf at hh1 hz1 hr1 hp1
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hh1
      · convert hz1 using 1; ring
      · exact hr1
      · convert hp1 using 1; ring
  obtain ⟨hh1, hz1, hr1, hp1⟩ := step1
  have step2 : h 2 = (-1/2) + (1/8)*R^(2 : ℕ) ∧
      z 2 = 0 ∧
      r 2 = (-2)*R^(1 : ℕ) + (1/2)*R^(3 : ℕ) ∧
      p 2 = 0 := by
    as_aux_lemma =>
      have hh2 := hh 1
      have hz2 := hz 1
      have hr2 := hr 1
      have hp2 := hp 1
      change h 2 = (-1/2) + (1/8)*R^(2 : ℕ) ∧
        z 2 = 0 ∧
        r 2 = (-2)*R^(1 : ℕ) + (1/2)*R^(3 : ℕ) ∧
        p 2 = 0
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
  have step3 : h 3 = 0 ∧
      z 3 = (2)*R^(1 : ℕ) + (3/2)*R^(3 : ℕ) ∧
      r 3 = 0 ∧
      p 3 = (-6) + (-2)*R^(2 : ℕ) + (3/8)*R^(4 : ℕ) := by
    as_aux_lemma =>
      have hh3 := hh 2
      have hz3 := hz 2
      have hr3 := hr 2
      have hp3 := hp 2
      change h 3 = 0 ∧
        z 3 = (2)*R^(1 : ℕ) + (3/2)*R^(3 : ℕ) ∧
        r 3 = 0 ∧
        p 3 = (-6) + (-2)*R^(2 : ℕ) + (3/8)*R^(4 : ℕ)
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2]
          at hh3 hz3 hr3 hp3
      ring_nf at hh3 hz3 hr3 hp3
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hh3
      · convert hz3 using 1; ring
      · exact hr3
      · convert hp3 using 1; ring
  obtain ⟨hh3, hz3, hr3, hp3⟩ := step3
  have step4 : h 4 = (7/4) + (-11/8)*R^(2 : ℕ) + (-1/64)*R^(4 : ℕ) ∧
      z 4 = 0 ∧
      r 4 = (16)*R^(1 : ℕ) + (-10)*R^(3 : ℕ) + (1/2)*R^(5 : ℕ) ∧
      p 4 = 0 := by
    as_aux_lemma =>
      have hh4 := hh 3
      have hz4 := hz 3
      have hr4 := hr 3
      have hp4 := hp 3
      change h 4 = (7/4) + (-11/8)*R^(2 : ℕ) + (-1/64)*R^(4 : ℕ) ∧
        z 4 = 0 ∧
        r 4 = (16)*R^(1 : ℕ) + (-10)*R^(3 : ℕ) + (1/2)*R^(5 : ℕ) ∧
        p 4 = 0
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3]
          at hh4 hz4 hr4 hp4
      ring_nf at hh4 hz4 hr4 hp4
      refine ⟨?_, ?_, ?_, ?_⟩
      · convert hh4 using 1; ring
      · exact hz4
      · convert hr4 using 1; ring
      · exact hp4
  obtain ⟨hh4, hz4, hr4, hp4⟩ := step4
  have step5 : h 5 = 0 ∧
      z 5 = (-16)*R^(1 : ℕ) + (-30)*R^(3 : ℕ) + (-13/2)*R^(5 : ℕ) ∧
      r 5 = 0 ∧
      p 5 = (48) + (34)*R^(2 : ℕ) + (-15)*R^(4 : ℕ) + (3/8)*R^(6 : ℕ) := by
    as_aux_lemma =>
      have hh5 := hh 4
      have hz5 := hz 4
      have hr5 := hr 4
      have hp5 := hp 4
      change h 5 = 0 ∧
        z 5 = (-16)*R^(1 : ℕ) + (-30)*R^(3 : ℕ) + (-13/2)*R^(5 : ℕ) ∧
        r 5 = 0 ∧
        p 5 = (48) + (34)*R^(2 : ℕ) + (-15)*R^(4 : ℕ) + (3/8)*R^(6 : ℕ)
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4]
          at hh5 hz5 hr5 hp5
      ring_nf at hh5 hz5 hr5 hp5
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hh5
      · convert hz5 using 1; ring
      · exact hr5
      · convert hp5 using 1; ring
  obtain ⟨hh5, hz5, hr5, hp5⟩ := step5
  have step6 : h 6 = (-139/8) + (889/32)*R^(2 : ℕ) + (95/128)*R^(4 : ℕ) + (51/512)*R^(6 : ℕ) ∧
      z 6 = 0 ∧
      r 6 = (-272)*R^(1 : ℕ) + (308)*R^(3 : ℕ) + (-35)*R^(5 : ℕ) + (3/4)*R^(7 : ℕ) ∧
      p 6 = 0 := by
    as_aux_lemma =>
      have hh6 := hh 5
      have hz6 := hz 5
      have hr6 := hr 5
      have hp6 := hp 5
      change h 6 = (-139/8) + (889/32)*R^(2 : ℕ) + (95/128)*R^(4 : ℕ) + (51/512)*R^(6 : ℕ) ∧
        z 6 = 0 ∧
        r 6 = (-272)*R^(1 : ℕ) + (308)*R^(3 : ℕ) + (-35)*R^(5 : ℕ) + (3/4)*R^(7 : ℕ) ∧
        p 6 = 0
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5]
          at hh6 hz6 hr6 hp6
      ring_nf at hh6 hz6 hr6 hp6
      refine ⟨?_, ?_, ?_, ?_⟩
      · convert hh6 using 1; ring
      · exact hz6
      · convert hr6 using 1; ring
      · exact hp6
  obtain ⟨hh6, hz6, hr6, hp6⟩ := step6
  have step7 : h 7 = 0 ∧
      z 7 = (272)*R^(1 : ℕ) + (924)*R^(3 : ℕ) + (455)*R^(5 : ℕ) + (189/4)*R^(7 : ℕ) ∧
      r 7 = 0 ∧
      p 7 = (-816) + (-992)*R^(2 : ℕ) + (756)*R^(4 : ℕ) + (-42)*R^(6 : ℕ) + (39/16)*R^(8 : ℕ) := by
    as_aux_lemma =>
      have hh7 := hh 6
      have hz7 := hz 6
      have hr7 := hr 6
      have hp7 := hp 6
      change h 7 = 0 ∧
        z 7 = (272)*R^(1 : ℕ) + (924)*R^(3 : ℕ) + (455)*R^(5 : ℕ) + (189/4)*R^(7 : ℕ) ∧
        r 7 = 0 ∧
        p 7 = (-816) + (-992)*R^(2 : ℕ) + (756)*R^(4 : ℕ) + (-42)*R^(6 : ℕ) + (39/16)*R^(8 : ℕ)
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6]
          at hh7 hz7 hr7 hp7
      ring_nf at hh7 hz7 hr7 hp7
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hh7
      · convert hz7 using 1; ring
      · exact hr7
      · convert hp7 using 1; ring
  obtain ⟨hh7, hz7, hr7, hp7⟩ := step7
  have step8 : h 8 = (5473/16) + (-14677/16)*R^(2 : ℕ) + (-5397/128)*R^(4 : ℕ) + (-3213/256)*R^(6 : ℕ) + (849/4096)*R^(8 : ℕ) ∧
      z 8 = 0 ∧
      r 8 = (7936)*R^(1 : ℕ) + (-14080)*R^(3 : ℕ) + (2688)*R^(5 : ℕ) + (-126)*R^(7 : ℕ) + (9/2)*R^(9 : ℕ) ∧
      p 8 = 0 := by
    as_aux_lemma =>
      have hh8 := hh 7
      have hz8 := hz 7
      have hr8 := hr 7
      have hp8 := hp 7
      change h 8 = (5473/16) + (-14677/16)*R^(2 : ℕ) + (-5397/128)*R^(4 : ℕ) + (-3213/256)*R^(6 : ℕ) + (849/4096)*R^(8 : ℕ) ∧
        z 8 = 0 ∧
        r 8 = (7936)*R^(1 : ℕ) + (-14080)*R^(3 : ℕ) + (2688)*R^(5 : ℕ) + (-126)*R^(7 : ℕ) + (9/2)*R^(9 : ℕ) ∧
        p 8 = 0
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7]
          at hh8 hz8 hr8 hp8
      ring_nf at hh8 hz8 hr8 hp8
      refine ⟨?_, ?_, ?_, ?_⟩
      · convert hh8 using 1; ring
      · exact hz8
      · convert hr8 using 1; ring
      · exact hp8
  obtain ⟨hh8, hz8, hr8, hp8⟩ := step8
  have step9 : h 9 = 0 ∧
      z 9 = (-7936)*R^(1 : ℕ) + (-42240)*R^(3 : ℕ) + (-34944)*R^(5 : ℕ) + (-7938)*R^(7 : ℕ) + (-1017/2)*R^(9 : ℕ) ∧
      r 9 = 0 ∧
      p 9 = (23808) + (44224)*R^(2 : ℕ) + (-50880)*R^(4 : ℕ) + (4662)*R^(6 : ℕ) + (-585)*R^(8 : ℕ) + (27/8)*R^(10 : ℕ) := by
    as_aux_lemma =>
      have hh9 := hh 8
      have hz9 := hz 8
      have hr9 := hr 8
      have hp9 := hp 8
      change h 9 = 0 ∧
        z 9 = (-7936)*R^(1 : ℕ) + (-42240)*R^(3 : ℕ) + (-34944)*R^(5 : ℕ) + (-7938)*R^(7 : ℕ) + (-1017/2)*R^(9 : ℕ) ∧
        r 9 = 0 ∧
        p 9 = (23808) + (44224)*R^(2 : ℕ) + (-50880)*R^(4 : ℕ) + (4662)*R^(6 : ℕ) + (-585)*R^(8 : ℕ) + (27/8)*R^(10 : ℕ)
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8]
          at hh9 hz9 hr9 hp9
      ring_nf at hh9 hz9 hr9 hp9
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hh9
      · convert hz9 using 1; ring
      · exact hr9
      · convert hp9 using 1; ring
  obtain ⟨hh9, hz9, hr9, hp9⟩ := step9
  have step10 : h 10 = (-357721/32) + (5771821/128)*R^(2 : ℕ) + (797555/256)*R^(4 : ℕ) + (1562589/1024)*R^(6 : ℕ) + (-445725/8192)*R^(8 : ℕ) + (-26199/32768)*R^(10 : ℕ) ∧
      z 10 = 0 ∧
      r 10 = (-353792)*R^(1 : ℕ) + (902528)*R^(3 : ℕ) + (-254320)*R^(5 : ℕ) + (19404)*R^(7 : ℕ) + (-1485)*R^(9 : ℕ) + (117/4)*R^(11 : ℕ) ∧
      p 10 = 0 := by
    as_aux_lemma =>
      have hh10 := hh 9
      have hz10 := hz 9
      have hr10 := hr 9
      have hp10 := hp 9
      change h 10 = (-357721/32) + (5771821/128)*R^(2 : ℕ) + (797555/256)*R^(4 : ℕ) + (1562589/1024)*R^(6 : ℕ) + (-445725/8192)*R^(8 : ℕ) + (-26199/32768)*R^(10 : ℕ) ∧
        z 10 = 0 ∧
        r 10 = (-353792)*R^(1 : ℕ) + (902528)*R^(3 : ℕ) + (-254320)*R^(5 : ℕ) + (19404)*R^(7 : ℕ) + (-1485)*R^(9 : ℕ) + (117/4)*R^(11 : ℕ) ∧
        p 10 = 0
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8, hh9, hz9, hr9, hp9]
          at hh10 hz10 hr10 hp10
      ring_nf at hh10 hz10 hr10 hp10
      refine ⟨?_, ?_, ?_, ?_⟩
      · convert hh10 using 1; ring
      · exact hz10
      · convert hr10 using 1; ring
      · exact hp10
  obtain ⟨hh10, hz10, hr10, hp10⟩ := step10
  have step11 : h 11 = 0 ∧
      z 11 = (353792)*R^(1 : ℕ) + (2707584)*R^(3 : ℕ) + (3306160)*R^(5 : ℕ) + (1222452)*R^(7 : ℕ) + (167805)*R^(9 : ℕ) + (30591/4)*R^(11 : ℕ) ∧
      r 11 = 0 ∧
      p 11 = (-1061376) + (-2796032)*R^(2 : ℕ) + (4491696)*R^(4 : ℕ) + (-598224)*R^(6 : ℕ) + (120978)*R^(8 : ℕ) + (-1485)*R^(10 : ℕ) + (1341/16)*R^(12 : ℕ) := by
    as_aux_lemma =>
      have hh11 := hh 10
      have hz11 := hz 10
      have hr11 := hr 10
      have hp11 := hp 10
      change h 11 = 0 ∧
        z 11 = (353792)*R^(1 : ℕ) + (2707584)*R^(3 : ℕ) + (3306160)*R^(5 : ℕ) + (1222452)*R^(7 : ℕ) + (167805)*R^(9 : ℕ) + (30591/4)*R^(11 : ℕ) ∧
        r 11 = 0 ∧
        p 11 = (-1061376) + (-2796032)*R^(2 : ℕ) + (4491696)*R^(4 : ℕ) + (-598224)*R^(6 : ℕ) + (120978)*R^(8 : ℕ) + (-1485)*R^(10 : ℕ) + (1341/16)*R^(12 : ℕ)
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8, hh9, hz9, hr9, hp9, hh10, hz10, hr10, hp10]
          at hh11 hz11 hr11 hp11
      ring_nf at hh11 hz11 hr11 hp11
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hh11
      · convert hz11 using 1; ring
      · exact hr11
      · convert hp11 using 1; ring
  obtain ⟨hh11, hz11, hr11, hp11⟩ := step11
  have step12 : h 12 = (34988647/64) + (-395756081/128)*R^(2 : ℕ) + (-304210511/1024)*R^(4 : ℕ) + (-216096639/1024)*R^(6 : ℕ) + (198388377/16384)*R^(8 : ℕ) + (12392127/32768)*R^(10 : ℕ) + (1341999/262144)*R^(12 : ℕ) ∧
      z 12 = 0 ∧
      r 12 = (22368256)*R^(1 : ℕ) + (-77459200)*R^(3 : ℕ) + (29917888)*R^(5 : ℕ) + (-3280992)*R^(7 : ℕ) + (401544)*R^(9 : ℕ) + (-16731)*R^(11 : ℕ) + (387/4)*R^(13 : ℕ) ∧
      p 12 = 0 := by
    as_aux_lemma =>
      have hh12 := hh 11
      have hz12 := hz 11
      have hr12 := hr 11
      have hp12 := hp 11
      change h 12 = (34988647/64) + (-395756081/128)*R^(2 : ℕ) + (-304210511/1024)*R^(4 : ℕ) + (-216096639/1024)*R^(6 : ℕ) + (198388377/16384)*R^(8 : ℕ) + (12392127/32768)*R^(10 : ℕ) + (1341999/262144)*R^(12 : ℕ) ∧
        z 12 = 0 ∧
        r 12 = (22368256)*R^(1 : ℕ) + (-77459200)*R^(3 : ℕ) + (29917888)*R^(5 : ℕ) + (-3280992)*R^(7 : ℕ) + (401544)*R^(9 : ℕ) + (-16731)*R^(11 : ℕ) + (387/4)*R^(13 : ℕ) ∧
        p 12 = 0
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8, hh9, hz9, hr9, hp9, hh10, hz10, hr10, hp10, hh11, hz11, hr11, hp11]
          at hh12 hz12 hr12 hp12
      ring_nf at hh12 hz12 hr12 hp12
      refine ⟨?_, ?_, ?_, ?_⟩
      · convert hh12 using 1; ring
      · exact hz12
      · convert hr12 using 1; ring
      · exact hp12
  obtain ⟨hh12, hz12, hr12, hp12⟩ := step12
  have step13 : h 13 = 0 ∧
      z 13 = (-22368256)*R^(1 : ℕ) + (-232377600)*R^(3 : ℕ) + (-388932544)*R^(5 : ℕ) + (-206702496)*R^(7 : ℕ) + (-45374472)*R^(9 : ℕ) + (-4374513)*R^(11 : ℕ) + (-609831/4)*R^(13 : ℕ) ∧
      r 13 = 0 ∧
      p 13 = (67104768) + (237969664)*R^(2 : ℕ) + (-506862720)*R^(4 : ℕ) + (91339248)*R^(6 : ℕ) + (-26323440)*R^(8 : ℕ) + (513513)*R^(10 : ℕ) + (-122031/2)*R^(12 : ℕ) + (6111/16)*R^(14 : ℕ) := by
    as_aux_lemma =>
      have hh13 := hh 12
      have hz13 := hz 12
      have hr13 := hr 12
      have hp13 := hp 12
      change h 13 = 0 ∧
        z 13 = (-22368256)*R^(1 : ℕ) + (-232377600)*R^(3 : ℕ) + (-388932544)*R^(5 : ℕ) + (-206702496)*R^(7 : ℕ) + (-45374472)*R^(9 : ℕ) + (-4374513)*R^(11 : ℕ) + (-609831/4)*R^(13 : ℕ) ∧
        r 13 = 0 ∧
        p 13 = (67104768) + (237969664)*R^(2 : ℕ) + (-506862720)*R^(4 : ℕ) + (91339248)*R^(6 : ℕ) + (-26323440)*R^(8 : ℕ) + (513513)*R^(10 : ℕ) + (-122031/2)*R^(12 : ℕ) + (6111/16)*R^(14 : ℕ)
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8, hh9, hz9, hr9, hp9, hh10, hz10, hr10, hp10, hh11, hz11, hr11, hp11, hh12, hz12, hr12, hp12]
          at hh13 hz13 hr13 hp13
      ring_nf at hh13 hz13 hr13 hp13
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hh13
      · convert hz13 using 1; ring
      · exact hr13
      · convert hp13 using 1; ring
  obtain ⟨hh13, hz13, hr13, hp13⟩ := step13
  have step14 : h 14 = (-4784061619/128) + (144425158669/512)*R^(2 : ℕ) + (73336684785/2048)*R^(4 : ℕ) + (281360592513/8192)*R^(6 : ℕ) + (-91897207545/32768)*R^(8 : ℕ) + (-18226513305/131072)*R^(10 : ℕ) + (-2076072453/524288)*R^(12 : ℕ) + (82018251/2097152)*R^(14 : ℕ) := by
    as_aux_lemma =>
      have hh14 := hh 13
      change h 14 = (-4784061619/128) + (144425158669/512)*R^(2 : ℕ) + (73336684785/2048)*R^(4 : ℕ) + (281360592513/8192)*R^(6 : ℕ) + (-91897207545/32768)*R^(8 : ℕ) + (-18226513305/131072)*R^(10 : ℕ) + (-2076072453/524288)*R^(12 : ℕ) + (82018251/2097152)*R^(14 : ℕ)
      norm_num [scalarJetConvolution, scalarJetUnit, Finset.sum_range_succ, Nat.choose,
        hh0, hz0, hr0, hp0, hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2, hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4, hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6, hh7, hz7, hr7, hp7, hh8, hz8, hr8, hp8, hh9, hz9, hr9, hp9, hh10, hz10, hr10, hp10, hh11, hz11, hr11, hp11, hh12, hz12, hr12, hp12, hh13, hz13, hr13, hp13]
          at hh14
      ring_nf at hh14
      convert hh14 using 1; ring
  have hh14 := step14
  rw [eval_modularThetaODESourceJet_eq_formalJet]
  change (h (2*k.val+2)-(1/4:ℂ)*h (2*k.val))/2 = _
  fin_cases k <;> norm_num [modularThetaEvenSeamSourcePolynomial, hh0, hh2, hh4, hh6, hh8, hh10, hh12, hh14] <;> ring

end
end HTGeometry
