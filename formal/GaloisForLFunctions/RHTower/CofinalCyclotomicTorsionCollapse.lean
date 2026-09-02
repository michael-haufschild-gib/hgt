import GaloisForLFunctions.RHTower.XiDeck

/-!
# Cofinal cyclotomic torsion collapse

Persistent zeros at a strictly cofinal sequence of nontrivial cyclotomic points survive locally
uniform convergence. Their accumulation at one forces the entire holomorphic limit to vanish.
-/

namespace RHTower

open Complex Filter Set Topology

noncomputable section

def cofinalCyclotomicRoot (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) / (n : ℂ))

theorem cofinalCyclotomicRoot_ne_one {n : ℕ} (hn : 2 ≤ n) :
    cofinalCyclotomicRoot n ≠ 1 := by
  intro h
  have hcrit := (exp_two_pi_mul_div_eq_one_iff (Nat.zero_lt_of_lt hn) 1).mp
    (by simpa [cofinalCyclotomicRoot] using h)
  have hn1 : n = 1 := Nat.dvd_one.mp hcrit
  omega

theorem tendsto_cofinalCyclotomicRoot_of_strictMono
    {n : ℕ → ℕ} (hn : StrictMono n) :
    Tendsto (fun j => cofinalCyclotomicRoot (n j)) atTop (nhds 1) := by
  have hnTop : Tendsto n atTop atTop := hn.tendsto_atTop
  have hnReal : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hnTop
  have hinv : Tendsto (fun j => ((n j : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnReal
  have hscale : Tendsto (fun j => (2 * Real.pi) * ((n j : ℝ))⁻¹) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hinv
  have harg : Tendsto
      (fun j => (((2 * Real.pi) * ((n j : ℝ))⁻¹ : ℝ) : ℂ) * Complex.I)
      atTop (nhds 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).comp hscale |>.mul_const Complex.I
  convert harg.cexp using 1
  · funext j
    simp [cofinalCyclotomicRoot, div_eq_mul_inv]
    ring
  · simp

private theorem tendsto_at_of_tendstoLocallyUniformly
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hconv : TendstoLocallyUniformly F f atTop) (z : ℂ) :
    Tendsto (fun m => F m z) atTop (nhds (f z)) := by
  have hunif : TendstoUniformlyOn F f atTop ({z} : Set ℂ) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_singleton).mp
      hconv.tendstoLocallyUniformlyOn
  exact hunif.tendsto_at (Set.mem_singleton z)

/-- Exact CIT-2 collapse theorem for persistent cofinal cyclotomic torsion zeros. -/
theorem cofinalCyclotomicTorsionCollapse
    (n : ℕ → ℕ) (hn : StrictMono n) (hn2 : 2 ≤ n 0)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (_hF : ∀ m, Differentiable ℂ (F m)) (hf : Differentiable ℂ f)
    (hzero : ∀ j m, j ≤ m → F m (cofinalCyclotomicRoot (n j)) = 0)
    (hconv : TendstoLocallyUniformly F f atTop) :
    f = 0 := by
  have hn2all : ∀ j, 2 ≤ n j := fun j => hn2.trans (hn.monotone (Nat.zero_le j))
  have hzlim : Tendsto (fun j => cofinalCyclotomicRoot (n j)) atTop (nhds 1) :=
    tendsto_cofinalCyclotomicRoot_of_strictMono hn
  have hzne : ∀ j, cofinalCyclotomicRoot (n j) ≠ 1 :=
    fun j => cofinalCyclotomicRoot_ne_one (hn2all j)
  have hlimitZero : ∀ j, f (cofinalCyclotomicRoot (n j)) = 0 := by
    intro j
    have hlim := tendsto_at_of_tendstoLocallyUniformly hconv
      (cofinalCyclotomicRoot (n j))
    have hevent : ∀ᶠ m in atTop, F m (cofinalCyclotomicRoot (n j)) = 0 :=
      Filter.eventually_atTop.2 ⟨j, fun m hm => hzero j m hm⟩
    have hzeroLim : Tendsto (fun m => F m (cofinalCyclotomicRoot (n j))) atTop (nhds 0) :=
      Filter.Tendsto.congr' (hevent.mono fun m hm => hm.symm) tendsto_const_nhds
    exact tendsto_nhds_unique hlim hzeroLim
  have hana : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hpunc : Tendsto (fun j => cofinalCyclotomicRoot (n j)) atTop
      (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzlim, Eventually.of_forall hzne⟩
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ, f z = 0 :=
    hpunc.frequently ((Eventually.of_forall hlimitZero).frequently)
  have heq := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ (1 : ℂ)) hfreq
  funext z
  exact heq (Set.mem_univ z)

end

end RHTower
