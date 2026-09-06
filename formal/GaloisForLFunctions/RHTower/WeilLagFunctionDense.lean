import GaloisForLFunctions.RHTower.WeilLagFunctionOmega

/-!
# Which lag sets carry RH

The lag function is continuous, so a one-sided bound on any set of lags whose closure contains a
half-line bounds it on the half-line, and RH follows (one-sided criterion).  The lags
`k log p + l log q` of two distinct primes form a dense subgroup of `ℝ`, hence

`RH ⟺ Φ is bounded above on {log(p^k q^l) : k, l ∈ ℤ}`

for any two distinct primes `p, q`: the values of the lag function on the `{p,q}`-rationals decide
RH.  A single prime gives the discrete progression `m log p`, which is not dense, and there the
converse is open.
-/

open Real Filter Topology Set

namespace RHTower

noncomputable section

theorem continuous_weilLagFunctionReal : Continuous weilLagFunctionReal :=
  Complex.continuous_re.comp continuous_weilLagFunction_unconditional

/-- **Density transfer.**  A one-sided bound on a lag set whose closure contains a half-line
gives RH. -/
theorem riemannHypothesis_of_bddAbove_on_dense {S : Set ℝ} {L₀ M : ℝ}
    (hS : Ici L₀ ⊆ closure S) (hM : ∀ L ∈ S, weilLagFunctionReal L ≤ M) : RiemannHypothesis := by
  have hcl : ∀ L ∈ closure S, weilLagFunctionReal L ≤ M := by
    have : closure S ⊆ {L | weilLagFunctionReal L ≤ M} :=
      closure_minimal (fun L hL => hM L hL)
        (isClosed_le continuous_weilLagFunctionReal continuous_const)
    exact fun L hL => this hL
  obtain ⟨M', hM'⟩ := (isCompact_Icc (a := (0:ℝ)) (b := |L₀|)).bddAbove_image
    continuous_weilLagFunctionReal.continuousOn
  suffices h : ∀ L : ℝ, 0 ≤ L → weilLagFunctionReal L ≤ max M M' by
    refine riemannHypothesis_of_weilLagFunctionReal_le (M := max M M') fun L => ?_
    rcases le_or_gt 0 L with hL | hL
    · exact h L hL
    · rw [← weilLagFunctionReal_neg]; exact h (-L) (by linarith)
  intro L hL
  rcases le_or_gt L₀ L with h1 | h1
  · exact le_max_of_le_left (hcl L (hS h1))
  · exact le_max_of_le_right (hM' ⟨L, ⟨hL, le_trans h1.le (le_abs_self _)⟩, rfl⟩)

/-- The logarithms of two distinct primes generate a dense subgroup of `ℝ`. -/
theorem dense_addSubgroup_log_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Dense ((AddSubgroup.closure {Real.log p, Real.log q} : AddSubgroup ℝ) : Set ℝ) := by
  rcases AddSubgroup.dense_or_cyclic (AddSubgroup.closure {Real.log p, Real.log q}) with h | ⟨a, ha⟩
  · exact h
  · exfalso
    have hp' : Real.log p ∈ AddSubgroup.closure {a} := by
      rw [← ha]; exact AddSubgroup.subset_closure (by simp)
    have hq' : Real.log q ∈ AddSubgroup.closure {a} := by
      rw [← ha]; exact AddSubgroup.subset_closure (by simp)
    rw [AddSubgroup.mem_closure_singleton] at hp' hq'
    obtain ⟨m, hm⟩ := hp'
    obtain ⟨n, hn⟩ := hq'
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
    have hrel : (n : ℝ) * Real.log p = (m : ℝ) * Real.log q := by
      rw [← hm, ← hn, zsmul_eq_mul, zsmul_eq_mul]; ring
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [zero_zsmul] at hn
      linarith
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_zsmul] at hm
      linarith
    have hrel' : (n.natAbs : ℝ) * Real.log p = (m.natAbs : ℝ) * Real.log q := by
      have h := congrArg abs hrel
      rw [abs_mul, abs_mul, abs_of_pos hlogp, abs_of_pos hlogq, ← Int.cast_abs, ← Int.cast_abs,
        Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.cast_natCast, Int.cast_natCast] at h
      exact h
    have hpow : (p : ℝ) ^ n.natAbs = (q : ℝ) ^ m.natAbs := by
      have h1 : Real.log ((p : ℝ) ^ n.natAbs) = Real.log ((q : ℝ) ^ m.natAbs) := by
        rw [Real.log_pow, Real.log_pow]; exact hrel'
      have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
      have hq0 : (0:ℝ) < q := by exact_mod_cast hq.pos
      exact Real.log_injOn_pos (by simpa using pow_pos hp0 _) (by simpa using pow_pos hq0 _) h1
    have hpowN : p ^ n.natAbs = q ^ m.natAbs := by exact_mod_cast hpow
    have hnpos : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn0
    have hdvd : p ∣ q ^ m.natAbs := by rw [← hpowN]; exact dvd_pow_self p hnpos
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

/-- **Two primes decide RH.**  RH ⟺ the lag function is bounded above on the lags
`k log p + l log q`, i.e. on the `{p,q}`-rationals `p^k q^l`. -/
theorem riemannHypothesis_iff_bddAbove_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k l : ℤ,
      weilLagFunctionReal (k * Real.log p + l * Real.log q) ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_weilLagFunctionReal_bddAbove.mp h
    exact ⟨M, fun k l => hM _⟩
  · rintro ⟨M, hM⟩
    refine riemannHypothesis_of_bddAbove_on_dense
      (S := ((AddSubgroup.closure {Real.log p, Real.log q} : AddSubgroup ℝ) : Set ℝ)) (L₀ := 0)
      (M := M) ?_ ?_
    · rw [(dense_addSubgroup_log_primes hp hq hpq).closure_eq]; exact subset_univ _
    · intro L hL
      obtain ⟨k, l, hkl⟩ := AddSubgroup.mem_closure_pair.mp hL
      rw [← hkl, zsmul_eq_mul, zsmul_eq_mul]
      exact hM k l

/-- In arithmetic form: RH ⟺ the lag values at the `{p,q}`-rationals are bounded above. -/
theorem riemannHypothesis_iff_bddAbove_two_prime_rationals {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k l : ℤ,
      weilLagFunctionReal (Real.log ((p : ℝ) ^ k * (q : ℝ) ^ l)) ≤ M := by
  rw [riemannHypothesis_iff_bddAbove_two_primes hp hq hpq]
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq.pos
  have e : ∀ k l : ℤ, Real.log ((p : ℝ) ^ k * (q : ℝ) ^ l) = k * Real.log p + l * Real.log q := by
    intro k l
    rw [Real.log_mul (zpow_ne_zero _ hp0.ne') (zpow_ne_zero _ hq0.ne'), Real.log_zpow, Real.log_zpow]
  simp_rw [e]

end

end RHTower
