import GaloisForLFunctions.HTGeometry.ConstitutiveDivisibleFormationSelection
import GaloisForLFunctions.RHTower.ConnectedSymmetryBarrier

/-!
# Quantized approximate-formation selection

Formation powers need not equal a target exactly.  If they enter a neighborhood on which an
integer charge is stable, their charges agree exactly; unbounded formation depths then annihilate
the target charge.  Nonvanishing complex loops realize the stability neighborhood through the
native distance-to-zero floor, giving a concrete winding-selection theorem.
-/

open Complex
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Quantized approximate-formation selection.**  A power-additive integer charge that is stable
under a declared admission relation vanishes on every carrier admitting cofinally deep approximate
powers inside that relation. -/
theorem charge_eq_zero_of_unbounded_stable_approximatePowers
    {M : Type*} [Monoid M] (charge : M → ℤ)
    (hpow : ∀ (x : M) (n : ℕ), charge (x ^ n) = (n : ℤ) * charge x)
    (near : M → M → Prop) (hstable : ∀ {x y : M}, near x y → charge x = charge y)
    (x : M) (happrox : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ y : M, near (y ^ n) x) :
    charge x = 0 := by
  apply int_eq_zero_of_unbounded_natCast_dvd
  intro N
  obtain ⟨n, hn, y, hy⟩ := happrox N
  refine ⟨n, hn, ⟨charge y, ?_⟩⟩
  rw [← hpow]
  exact (hstable hy).symm

/-- **Global formation/properness law.**  Suppose formation depths tend to infinity while their
formed powers converge to one carrier.  If that carrier has one metric admission neighborhood on
which charge is constant, then its charge vanishes.  This is the sequential properness form of the
quantized approximate-formation selector. -/
theorem charge_eq_zero_of_cofinal_approximatePowers
    {M : Type*} [Monoid M] [PseudoMetricSpace M] (charge : M → ℤ)
    (hpow : ∀ (x : M) (n : ℕ), charge (x ^ n) = (n : ℤ) * charge x)
    (x : M) {depth : ℕ → ℕ} {root : ℕ → M}
    (hdepth : Tendsto depth atTop atTop)
    (hformed : Tendsto (fun k => root k ^ depth k) atTop (𝓝 x))
    (ε : ℝ) (hε : 0 < ε)
    (hstable : ∀ z : M, dist z x < ε → charge z = charge x) :
    charge x = 0 := by
  apply int_eq_zero_of_unbounded_natCast_dvd
  intro N
  have hdepthN : ∀ᶠ k : ℕ in atTop, N ≤ depth k :=
    tendsto_atTop.1 hdepth N
  have hclose : ∀ᶠ k : ℕ in atTop, dist (root k ^ depth k) x < ε :=
    Metric.tendsto_nhds.1 hformed ε hε
  obtain ⟨k, hkN, hkclose⟩ := (hdepthN.and hclose).exists
  refine ⟨depth k, hkN, ⟨charge (root k), ?_⟩⟩
  rw [← hpow]
  exact (hstable _ hkclose).symm

/-- Vanishing formation/recovery interchange defect transfers convergence of recovered formed
packets to convergence of observer powers. -/
theorem tendsto_recoveredPowers_of_formationInterchange
    {S M : Type*} [Monoid M] [PseudoMetricSpace M]
    (recover : S → M) (packet formed : ℕ → S) (depth : ℕ → ℕ) (x : M)
    (hformed : Tendsto (fun k => recover (formed k)) atTop (𝓝 x))
    (hinterchange : Tendsto
      (fun k => dist ((recover (packet k)) ^ depth k) (recover (formed k))) atTop (𝓝 0)) :
    Tendsto (fun k => (recover (packet k)) ^ depth k) atTop (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hformed' : ∀ᶠ k : ℕ in atTop, dist (recover (formed k)) x < ε / 2 :=
    Metric.tendsto_nhds.1 hformed (ε / 2) hhalf
  have hinterchange' : ∀ᶠ k : ℕ in atTop,
      dist (dist ((recover (packet k)) ^ depth k) (recover (formed k))) 0 < ε / 2 :=
    Metric.tendsto_nhds.1 hinterchange (ε / 2) hhalf
  filter_upwards [hformed', hinterchange'] with k hkformed hkinterchange
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at hkinterchange
  calc
    dist ((recover (packet k)) ^ depth k) x ≤
        dist ((recover (packet k)) ^ depth k) (recover (formed k)) +
          dist (recover (formed k)) x := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hkinterchange hkformed
    _ = ε := by ring

/-- **Formation/recovery interchange selection.**  Cofinal source formation, convergence after
recovery, asymptotic commutation of recovery with powers, and one native charge-stable admission
gap force the recovered target charge to vanish. -/
theorem charge_eq_zero_of_recovered_formationInterchange
    {S M : Type*} [Monoid M] [PseudoMetricSpace M]
    (charge : M → ℤ)
    (hpow : ∀ (z : M) (n : ℕ), charge (z ^ n) = (n : ℤ) * charge z)
    (recover : S → M) (packet formed : ℕ → S) (depth : ℕ → ℕ) (x : M)
    (hdepth : Tendsto depth atTop atTop)
    (hformed : Tendsto (fun k => recover (formed k)) atTop (𝓝 x))
    (hinterchange : Tendsto
      (fun k => dist ((recover (packet k)) ^ depth k) (recover (formed k))) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε)
    (hstable : ∀ z : M, dist z x < ε → charge z = charge x) :
    charge x = 0 := by
  apply charge_eq_zero_of_cofinal_approximatePowers charge hpow x hdepth
    (tendsto_recoveredPowers_of_formationInterchange
      recover packet formed depth x hformed hinterchange) ε hε hstable

/-- **Cofinal approximate-power winding selection.**  If one nonvanishing loop is approximated at
unbounded power depths more accurately than its native floor from zero, then its winding number is
zero.  Exact roots, convergence of approximants, and a common approximating loop are unnecessary. -/
theorem windingNumber_eq_zero_of_unbounded_approximatePowers
    {γ : ℝ → ℂ} {a b m : ℝ} (hγ : RHTower.IsLoop γ a b)
    (hm : ∀ t, m ≤ ‖γ t‖)
    (happrox : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ η : ℝ → ℂ,
      RHTower.IsLoop η a b ∧ ∀ t, ‖η t ^ n - γ t‖ < m) :
    RHTower.windingNumber γ a b = 0 := by
  apply int_eq_zero_of_unbounded_natCast_dvd
  intro N
  obtain ⟨n, hn, η, hη, hclose⟩ := happrox N
  let ηpow : ℝ → ℂ := fun t => η t ^ n
  have hηpow : RHTower.IsLoop ηpow a b :=
    ⟨hη.continuous.pow n, fun t => pow_ne_zero n (hη.nonzero t), by
      simp only [ηpow, hη.closed]⟩
  have heq : RHTower.windingNumber ηpow a b = RHTower.windingNumber γ a b :=
    RHTower.windingNumber_eq_of_close hγ.continuous hηpow.continuous hγ.closed hηpow.closed
      hm hclose
  have hpower : RHTower.windingNumber ηpow a b =
      (n : ℤ) * RHTower.windingNumber η a b := by
    simpa [ηpow] using RHTower.windingNumber_pow hη n
  refine ⟨n, hn, ⟨RHTower.windingNumber η a b, ?_⟩⟩
  exact heq.symm.trans hpower

/-- **Quantitative formation-gap obstruction.**  If a target loop has nonzero winding and the
formation depth exceeds its absolute winding, every power loop must meet or cross the target's
native distance-to-zero floor somewhere. -/
theorem exists_windingFormationGap
    {γ η : ℝ → ℂ} {a b m : ℝ} {n : ℕ}
    (hγ : RHTower.IsLoop γ a b) (hη : RHTower.IsLoop η a b)
    (hm : ∀ t, m ≤ ‖γ t‖)
    (hwind : RHTower.windingNumber γ a b ≠ 0)
    (hdepth : (RHTower.windingNumber γ a b).natAbs < n) :
    ∃ t, m ≤ ‖η t ^ n - γ t‖ := by
  by_contra hgap
  push Not at hgap
  let ηpow : ℝ → ℂ := fun t => η t ^ n
  have hηpow : RHTower.IsLoop ηpow a b :=
    ⟨hη.continuous.pow n, fun t => pow_ne_zero n (hη.nonzero t), by
      simp only [ηpow, hη.closed]⟩
  have heq : RHTower.windingNumber ηpow a b = RHTower.windingNumber γ a b :=
    RHTower.windingNumber_eq_of_close hγ.continuous hηpow.continuous hγ.closed hηpow.closed
      hm hgap
  have hpower : RHTower.windingNumber ηpow a b =
      (n : ℤ) * RHTower.windingNumber η a b := by
    simpa [ηpow] using RHTower.windingNumber_pow hη n
  have hdvd : (n : ℤ) ∣ RHTower.windingNumber γ a b :=
    ⟨RHTower.windingNumber η a b, heq.symm.trans hpower⟩
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hwind
  simpa using (not_le_of_gt hdepth hle)

/-- Closed capstone exposing both universal charge selection and its native winding realization. -/
theorem approximateFormationSelection_capstone :
    (∀ {M : Type*} [Monoid M] (charge : M → ℤ),
      (∀ (x : M) (n : ℕ), charge (x ^ n) = (n : ℤ) * charge x) →
      ∀ (near : M → M → Prop),
      (∀ {x y : M}, near x y → charge x = charge y) →
      ∀ x : M, (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ y : M, near (y ^ n) x) → charge x = 0) := by
  intro M _ charge hpow near hstable x happrox
  exact charge_eq_zero_of_unbounded_stable_approximatePowers
    charge hpow near hstable x happrox

end GaloisForLFunctions.HTGeometry
