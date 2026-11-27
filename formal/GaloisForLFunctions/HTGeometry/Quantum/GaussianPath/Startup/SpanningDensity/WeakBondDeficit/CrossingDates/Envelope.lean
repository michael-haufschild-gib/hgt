import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.CrossingDates.InitialInterval
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.StartupLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin

/-! # First robust crossing between the two times dictated by the bond deficit -/

open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open PrescribedTimes
noncomputable section

private theorem root_tenth (x : ℝ) (hx : 0≤x) : (x^10)^(1/10:ℝ)=x := by
  rw [←rpow_natCast,←rpow_mul hx]
  norm_num

/-- A budget missing d bonds is affordable up to the lower endpoint.
At the upper endpoint even a quarter-error circuit exceeds this budget.
Thus every intermediate robust level has its first crossing in this interval. -/
theorem gaussian_crossing_envelope :
    ∃ M≥(1:ℝ), ∃ a>0, ∃ b>0, ∃ γ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
      ∀ (d : ℕ) (h : ℝ), d≤n+1 → (d:ℝ)=K*h^9 → (d:ℝ)≤γ*K → 0<h → M*h≤1 →
        let t₀ := a/(K*(M*h)^10)
        let t₁ := a/(K*(h/M)^10)
        K*t₁^2≤b → ∀ ρ∈Ioc (1/20:ℝ) (1/4),
          crossingOrigin n (n+1-d) ρ x∈Icc t₀ t₁ := by
  obtain ⟨a,ha,b,hb,c,hc,C,hC,hcost⟩ := gaussian_startup_deficit
  obtain ⟨γ,hγ,hinit⟩ := gaussian_initial_saving a ha
  let M := max 1 (max (1/c) (2*C))
  have hM : 1≤M := le_max_left ..
  have hM' : 0<M := zero_lt_one.trans_le hM
  have hpow : M≤M^9 := by
    calc M = M^1 := (pow_one M).symm
         _ ≤ _ := pow_le_pow_right₀ hM (by decide)
  have hMc : 1≤c*M^9 := by
    have hm := ((le_max_left (1/c) (2*C)).trans (le_max_right ..)).trans hpow
    have h := (div_le_iff₀ hc).mp hm
    linarith only [h]
  have hMC : 2*C≤M^9 := ((le_max_right (1/c) (2*C)).trans (le_max_right ..)).trans hpow
  refine ⟨M,hM,a,ha,b,hb,γ,hγ,?_⟩
  filter_upwards [hcost,hinit] with ω hw hi
  filter_upwards [hw,hi] with n hn hi
  intro K x d h hdn hd hγd hh hsmall t₀ t₁ hwindow ρ hρ
  let u := pathPauliDisorderShell ω n
  let m := n+1-d
  have hK : 0<K := by dsimp only [K]; positivity
  have hbudget : (m:ℝ)+(d:ℝ)=K-1 := by
    dsimp only [m,K]
    rw [Nat.cast_sub hdn]
    push_cast
    ring
  have hmh := mul_pos hM' hh
  have hdiv := div_pos hh hM'
  have hrel : h/M≤M*h := (div_le_self hh.le hM).trans (le_mul_of_one_le_left hh.le hM)
  have h₀ : 0<t₀ := div_pos ha (mul_pos hK (pow_pos hmh _))
  have h₁ : 0<t₁ := div_pos ha (mul_pos hK (pow_pos hdiv _))
  have hord : t₀≤t₁ := div_le_div_of_nonneg_left ha.le (mul_pos hK (pow_pos hdiv _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdiv.le hrel 10) hK.le)
  have dist (r : ℝ) : pathGateDistance n m x r=Metric.infDist (unitaryEvolution (pathHamiltonian u) r)
      (phaseCircuitMatrixImageAtMost (n+2) m) := by
    rw [pathGateDistance,numberedGenerator_shell (pathPauliDisorderShell ω n)]
  have early (r : ℝ) (hr : r∈Icc 0 t₀) :
      HasProjectiveCircuitApproximation (n+2) (1/20) m (unitaryEvolution (pathHamiltonian u) r) := by
    by_cases hstart : K * |r|≤a
    · exact hi r hstart d hγd
    have hKr := ha.trans (lt_of_not_ge hstart)
    have htime := (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.1 (hr.2.trans hord) 2) hK.le).trans hwindow
    obtain ⟨s,hs,hdef,_⟩ := hn r (le_of_not_ge hstart) htime (1/20) (by constructor <;> norm_num)
    let y := (a/(K * |r|))^(1/10:ℝ)
    have hbase : (M*h)^10≤a/(K * |r|) := by
      apply (le_div_iff₀ hKr).mpr
      rw [abs_of_nonneg hr.1]
      have he := (le_div_iff₀ (mul_pos hK (pow_pos hmh 10))).mp hr.2
      linarith only [he]
    have hy : M*h≤y := (root_tenth _ hmh.le).ge.trans
      (rpow_le_rpow (pow_nonneg hmh.le 10) hbase (by norm_num))
    have hd' : (d:ℝ)≤c*K*y^9 := calc
      _ = K*h^9 := hd
      _ ≤ (c*M^9)*(K*h^9) := le_mul_of_one_le_left (by positivity) hMc
      _ = c*K*(M*h)^9 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmh.le hy 9) (mul_nonneg hc.le hK.le)
    change c*K*y^9≤K-1-s at hdef
    have hs' : (s:ℝ) ≤ (m:ℝ) := by linarith only [hbudget,hd',hdef]
    obtain ⟨z,hz,D,hD,hfit⟩ := hs.1
    exact ⟨z,hz,D,hD.trans (Nat.cast_le.mp hs'),hfit⟩
  have late : ¬HasProjectiveCircuitApproximation (n+2) (1/4) m (unitaryEvolution (pathHamiltonian u) t₁) := by
    have hclock : K * |t₁|=a/(h/M)^10 := by
      rw [abs_of_pos h₁]
      dsimp only [t₁]
      field_simp
    have hstart : a≤K * |t₁| := by
      rw [hclock,le_div_iff₀ (pow_pos hdiv _)]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hdiv.le (hrel.trans hsmall)) ha.le).trans_eq (mul_one _)
    obtain ⟨s,hs,_,hu⟩ := hn t₁ hstart hwindow (1/4) (by constructor <;> norm_num)
    have hy : (a/(K * |t₁|))^(1/10:ℝ)=h/M := by
      rw [hclock,show a/(a/(h/M)^10)=(h/M)^10 by field_simp,root_tenth _ hdiv.le]
    change K-1-s≤C*K*((a/(K * |t₁|))^(1/10:ℝ))^9 at hu
    rw [hy] at hu
    have hhalf : 2*(C*K*(h/M)^9)≤d := by
      rw [hd,div_pow]
      calc
        _ = (2*C)*(K*h^9)/M^9 := by ring
        _ ≤ (M^9)*(K*h^9)/M^9 := by gcongr
        _ = _ := by field_simp
    intro hf
    have hle := (Nat.cast_le (α:=ℝ)).mpr (hs.2 hf)
    have hdp : 0<(d:ℝ) := by rw [hd]; positivity
    linarith only [hle,hbudget,hu,hhalf,hdp]
  let E := {r : ℝ | 0≤r ∧ ρ≤pathGateDistance n m x r}
  have hlate : t₁∈E := by
    refine ⟨h₁.le,hρ.2.trans ?_⟩
    rw [dist]
    exact (lt_of_not_ge (fun he => late ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr he))).le
  change sInf E∈Icc t₀ t₁
  refine ⟨le_csInf ⟨t₁,hlate⟩ ?_,csInf_le ⟨0,fun _ hr => hr.1⟩ hlate⟩
  intro r hr
  by_contra! hlt
  have he := (hasProjectiveCircuitApproximation_iff_infDist ..).mp (early r ⟨hr.1,hlt.le⟩)
  rw [←dist] at he
  linarith only [hr.2,hρ.1,he]

#print axioms gaussian_crossing_envelope
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
