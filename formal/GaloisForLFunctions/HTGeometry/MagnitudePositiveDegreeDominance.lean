import GaloisForLFunctions.HTGeometry.MagnitudeBalancedWitnessBounds
import GaloisForLFunctions.HTGeometry.MagnitudeSupportDominance

/-!
# Integer-dominance data for positive-jet-degree relations

For a fixed differential polynomial with positive maximal jet degree, a balanced nonzero grouped
atom exists at every sufficiently high probe.  Selecting a nonzero-weight valuation minimizer,
the balanced witness bounds its largest source index; the conserved index mass then forces maximal
jet degree and one-sided tail support.  Tail super-increasing separation applies to every other
nonzero weight, including smaller-degree competitors, and the gap beats the polynomial weight mass.
-/

open Filter Finset PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- Complete support-restricted integer-dominance data for any polynomial whose maximal jet degree
is positive.  The conclusion itself is coefficient-ring independent; integrality is consumed only
later by `aeval_coeff_ne_zero_of_int_dominant_on_support`. -/
theorem exists_logSuperlacunary_intDominance_of_positiveJetDegree {b : ℕ → ℝ}
    (hbpos : ∀ i, 0 < b i)
    (hratio : Tendsto (fun i => b (i + 1) / b i) atTop atTop)
    {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ (N : ℕ) (ν₀ : ℕ →₀ ℕ) (G : ℝ),
      ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q ν₀ ≠ 0 ∧
      (∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
          ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤
            ν.sum (fun i k => (k : ℝ) * b i)) ∧
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) <
        Real.exp G := by
  classical
  let D := magnitudeMaxJetDegree n Q
  let O := magnitudeMaxJetOrder n Q
  let Z := magnitudeMaxXDegree Q
  have hD : 0 < D := hDpos
  have hsupport : Q.support.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have : D = 0 := by simp [D, magnitudeMaxJetDegree, hempty]
    omega
  obtain ⟨anchor, ha, hanchor⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupport (fun m => jetMonomialDegree n m)
  have hanchorD : jetMonomialDegree n anchor = D := by
    rw [D, magnitudeMaxJetDegree, jetMonomialDegree]
    exact hanchor.symm
  have hanchorPos : 0 < jetMonomialDegree n anchor := hanchorD ▸ hD
  obtain ⟨δ, _hδinj, Qbal, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight ha hanchorPos
  let B := magnitudeOffsetMax δ
  let J := jetMonomialOrder n anchor
  obtain ⟨Qwit, hwitnessVal⟩ :=
    exists_eventually_balancedKey_valuation_le_succ hbpos hratio δ
  have hpos : ∀ᶠ i in atTop, 0 < b i := Filter.Eventually.of_forall hbpos
  obtain ⟨Nstrict, hbstrict⟩ := exists_eventually_strictMono hpos hratio
  obtain ⟨Nsi, hsi⟩ := exists_superIncreasing_of_ratio hbpos hratio D
  let A : ℝ := magnitudeCoefficientMass Q * (((O + 1) ^ O : ℕ) : ℝ)
  let E := D + O
  have hCoeffMass : 0 < magnitudeCoefficientMass Q := by
    rw [magnitudeCoefficientMass]
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨anchor, ha, norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp ha)⟩
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos hCoeffMass (by positivity)
  let L := D * (B + 1) + anchor 0 + 1
  let Cmass := 2 * L
  have hL : 0 < L := by dsimp [L]; omega
  have hCmass : 0 < Cmass := by dsimp [Cmass]; omega
  obtain ⟨Mmass, hmassExp⟩ :=
    exists_const_mul_pow_lt_exp_div_of_ratio hpos hratio A hA Cmass E D hCmass
  let Cgeom := J + Z + (D - 1) * (B + 1)
  let S₀ := Qbal + Qwit + Nstrict + Nsi + Mmass + Cgeom + 1
  let q := 2 * S₀
  let T := q / 2
  let s : Fin D → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - J
  have hT : T = S₀ := by simp [T, q]
  have hqQbal : Qbal ≤ q := by dsimp [q, S₀]; omega
  have hqQwit : Qwit ≤ q := by dsimp [q, S₀]; omega
  have hTNstrict : Nstrict ≤ T := by rw [hT]; dsimp [S₀]; omega
  have hTNsi : Nsi ≤ T := by rw [hT]; dsimp [S₀]; omega
  have hTMmass : Mmass ≤ T := by rw [hT]; dsimp [S₀]; omega
  have hqJ : J ≤ q := by dsimp [q, S₀, Cgeom]; omega
  have hqgeom : Cgeom < q := by dsimp [q, S₀]; omega
  have hTgeom : T + Cgeom ≤ q := by rw [hT]; dsimp [q, S₀]; omega
  obtain ⟨hνw, hww, _hgroup⟩ :
      key s ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
        aevalWeight n N Q (key s) ≠ 0 ∧
        balancedJetGroup n N D Q s = topShiftJetGroup n Q anchor := by
    simpa [s, N, D, J] using hbalanced q hqQbal
  obtain ⟨hVw, hVwSucc⟩ := hwitnessVal q hqQwit
  change (key s).sum (fun i k => (k : ℝ) * b i) ≤ (D : ℝ) * b (q + B) at hVw
  change (D : ℝ) * b (q + B) ≤ b (q + B + 1) at hVwSucc
  obtain ⟨ν₀, hν₀, hw₀, hmin, hminw⟩ := exists_min_nonzero_aevalWeight Q b hνw hww
  have hVupper : ν₀.sum (fun i k => (k : ℝ) * b i) ≤ b (q + B + 1) :=
    hminw.trans (hVw.trans hVwSucc)
  have hsLower : D * q ≤ ∑ i, s i := by
    calc
      D * q = ∑ _i : Fin D, q := by simp
      _ ≤ ∑ i : Fin D, s i := by
        apply Finset.sum_le_sum
        intro i _
        simp [s]
  have hJsum : J ≤ (∑ i, s i) + anchor 0 := by
    have hqsum : q ≤ ∑ i, s i := by
      have hD1 : 1 ≤ D := hD
      omega
    omega
  have hNadd : N + J = (∑ i, s i) + anchor 0 := by
    dsimp [N]
    exact Nat.sub_add_cancel hJsum
  have hDqN : D * q ≤ N + J := by rw [hNadd]; omega
  have hNZ : Z < N := by
    have hZJq : Z + J < q := by
      have : J + Z < Cgeom + 1 := by dsimp [Cgeom]; omega
      omega
    have hqD : q ≤ D * q := by
      have hD1 : 1 ≤ D := hD
      exact Nat.mul_le_mul_right q hD1
    omega
  have hν₀support := appearing_atom_support_nonempty_of_maxX_lt_level Q hν₀ hNZ
  have hNstrictK : Nstrict ≤ q + B + 1 := hTNstrict.trans (by omega)
  have hmax : ν₀.support.max' hν₀support ≤ q + B + 1 :=
    support_max_le_of_valuation_le (fun i => (hbpos i).le) hbstrict hν₀support
      hNstrictK hVupper
  have hcount_le := appearing_atom_count_le Q hν₀
  change ν₀.sum (fun _ k => k) ≤ D at hcount_le
  have hweight_lower := (appearing_atom_weighted_sum_bounds Q hν₀).1
  change N - Z ≤ ν₀.sum (fun i k => i * k) at hweight_lower
  have hcount : ν₀.sum (fun _ k => k) = D := by
    apply Nat.le_antisymm hcount_le
    by_contra hnot
    have hcountSmall : ν₀.sum (fun _ k => k) ≤ D - 1 := by omega
    have hweightMax := weighted_sum_le_max_mul_count hν₀support
    have hupper : ν₀.sum (fun i k => i * k) ≤ (q + B + 1) * (D - 1) :=
      hweightMax.trans <| (Nat.mul_le_mul hmax hcountSmall)
    have hgeomExpand :
        Z + (q + B + 1) * (D - 1) + J =
          (D - 1) * q + Cgeom := by
      dsimp [Cgeom]
      ring
    have hDexpand : (D - 1) * q + q = D * q := by
      have hDeq : D - 1 + 1 = D := by omega
      rw [← hDeq]
      ring
    have htooLarge : Z + (q + B + 1) * (D - 1) + J < D * q := by
      rw [hgeomExpand, ← hDexpand]
      exact Nat.add_lt_add_left hqgeom _
    have : Z + (q + B + 1) * (D - 1) < N := by omega
    omega
  have htailArith : T + (D - 1) * (q + B + 1) ≤ N - Z := by
    have hgeomExpand :
        T + (D - 1) * (q + B + 1) + Z + J =
          (D - 1) * q + (T + Cgeom) := by
      dsimp [Cgeom]
      ring
    have hDexpand : (D - 1) * q + q = D * q := by
      have hDeq : D - 1 + 1 = D := by omega
      rw [← hDeq]
      ring
    have hle : T + (D - 1) * (q + B + 1) + Z + J ≤ D * q := by
      rw [hgeomExpand, ← hDexpand]
      exact Nat.add_le_add_left hTgeom _
    omega
  have hν₀tail : ∀ i, ν₀ i ≠ 0 → T ≤ i :=
    finsupp_tailSupport_of_count_weight_max hcount hweight_lower hν₀support hmax htailArith
  have hsiT : ∀ k, T ≤ k →
      ((D : ℝ) + 1) * (∑ i ∈ Finset.range k, b i) ≤ b k :=
    fun k hk => hsi k (hTNsi.trans hk)
  have hgap : ∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
      aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
        ν₀.sum (fun i k => (k : ℝ) * b i) + b T / ((D : ℝ) + 1) ≤
          ν.sum (fun i k => (k : ℝ) * b i) := by
    intro ν hν hw hne
    have hνbound := appearing_atom_apply_le Q hν
    change ∀ i, ν i ≤ D at hνbound
    have hν₀bound := appearing_atom_apply_le Q hν₀
    change ∀ i, ν₀ i ≤ D at hν₀bound
    have hνcount := appearing_atom_count_le Q hν
    change ν.sum (fun _ k => k) ≤ D at hνcount
    have hνmin := hmin ν hν hw
    have hpair : ∃ K : ℕ, T ≤ K ∧
        ν₀.sum (fun i k => (k : ℝ) * b i) + b K / ((D : ℝ) + 1) ≤
          ν.sum (fun i k => (k : ℝ) * b i) := by
      rcases lt_or_eq_of_le hνcount with hlt | heq
      · exact valuation_gap_above_min_of_count_lt_tailSupport
          (fun i => (hbpos i).le) hsiT hνbound hν₀bound (hcount ▸ hlt)
          hν₀tail hνmin
      · exact valuation_gap_above_min_of_count_eq_tailSupport
          (fun i => (hbpos i).le) hsiT hνbound hν₀bound (heq.trans hcount.symm)
          hν₀tail hne hνmin
    obtain ⟨K, hTK, hpair⟩ := hpair
    have hbTK : b T ≤ b K := by
      rcases hTK.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact (hbstrict T K hTNstrict hlt).le
    have hdiv : b T / ((D : ℝ) + 1) ≤ b K / ((D : ℝ) + 1) := by
      exact div_le_div_of_nonneg_right hbTK (by positivity)
    linarith
  have hsUpper : (∑ i, s i) ≤ D * (q + B) := by
    calc
      ∑ i : Fin D, s i ≤ ∑ _i : Fin D, (q + B) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [s]
        exact Nat.add_le_add_left (offset_le_magnitudeOffsetMax δ i) q
      _ = D * (q + B) := by simp
  have hNupper : N + 1 ≤ D * (q + B) + anchor 0 + 1 := by
    dsimp [N]
    omega
  have hqT : q = 2 * T := by rw [hT]; simp [q]
  have hlevelL : N + 1 ≤ L * (q + 1) := by
    have hbase : q + B ≤ (B + 1) * (q + 1) := by nlinarith
    have hjet : D * (q + B) ≤ D * (B + 1) * (q + 1) := by
      calc
        D * (q + B) ≤ D * ((B + 1) * (q + 1)) := Nat.mul_le_mul_left D hbase
        _ = D * (B + 1) * (q + 1) := by ring
    have hconst : anchor 0 + 1 ≤ (anchor 0 + 1) * (q + 1) := by nlinarith
    dsimp [L]
    nlinarith
  have hlevel : N + 1 ≤ Cmass * (T + 1) := by
    have hqt : q + 1 ≤ 2 * (T + 1) := by rw [hqT]; omega
    calc
      N + 1 ≤ L * (q + 1) := hlevelL
      _ ≤ L * (2 * (T + 1)) := Nat.mul_le_mul_left L hqt
      _ = Cmass * (T + 1) := by dsimp [Cmass]; ring
  have hpoly := hmassExp T hTMmass
  have hmass :
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) <
        Real.exp (b T / ((D : ℝ) + 1)) := by
    calc
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
          ≤ magnitudeCoefficientMass Q * (((O + 1) ^ O : ℕ) : ℝ) *
              (((N + 1) ^ E : ℕ) : ℝ) := by
            simpa [D, O, E] using aevalWeight_mass_le_singlePolynomial n Q N
      _ = A * ((N + 1 : ℝ) ^ E) := by
            dsimp [A]
            push_cast
            ring
      _ ≤ A * ((Cmass : ℝ) * ((T : ℝ) + 1)) ^ E := by
            apply mul_le_mul_of_nonneg_left _ hA.le
            apply pow_le_pow_left₀ (by positivity)
            exact_mod_cast hlevel
      _ < Real.exp (b T / ((D : ℝ) + 1)) := hpoly
  exact ⟨N, ν₀, b T / ((D : ℝ) + 1), hν₀, hw₀, hgap, hmass⟩

end

end GaloisForLFunctions
