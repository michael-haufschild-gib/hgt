import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCoherentGraphHankelWeld

/-!
# Arithmetic tail charge of the completed unit-Riesz coherent response

The exponential increment kernel has a constant right-tail mode.  For a finite packet its charge
is `sum c_p (1-exp(-p/2))`.  Applied to the literal unit-Riesz source, prime charge is exactly half
prime coherent energy, while the polar continuum response is computed in closed form.

At integer aperture `N`, completed prime-minus-polar response therefore tends to

`criticalMellinChebyshevResolventSource (log N) / 2`.

Thus direct graph/Hankel leakage decays exactly when the completed arithmetic resolvent vanishes.
Whenever it does not, squared amplitude is nonintegrable and the literal completed amplitude is not
an HG leak profile.  Any lawful FU/UR-to-HG transport must remove this charge by a source-faithful
codiagonal or aperture difference; direct embedding is impossible.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

theorem unitExponentialIncrementKernel_eq_rightTail
    {p u : ℝ} (hpu : p ≤ u) :
    unitExponentialIncrementKernel p u =
      (1 - Real.exp (-p / 2)) +
        Real.exp (-u / 2) * (Real.exp (p / 2) - 1) := by
  have habs : |p - u| = u - p := by
    rw [abs_of_nonpos (sub_nonpos.mpr hpu)]
    ring
  rw [unitExponentialIncrementKernel, habs]
  have he : Real.exp (-(u - p) / 2) =
      Real.exp (-u / 2) * Real.exp (p / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

def unitExponentialFiniteKernelResponse {ι : Type*} [Fintype ι]
    (c p : ι → ℝ) (u : ℝ) : ℝ :=
  ∑ i, c i * unitExponentialIncrementKernel (p i) u

def unitExponentialFiniteKernelTailCharge {ι : Type*} [Fintype ι]
    (c p : ι → ℝ) : ℝ :=
  ∑ i, c i * (1 - Real.exp (-(p i) / 2))

def unitExponentialFiniteKernelTailMode {ι : Type*} [Fintype ι]
    (c p : ι → ℝ) : ℝ :=
  ∑ i, c i * (Real.exp (p i / 2) - 1)

theorem unitExponentialFiniteKernelResponse_eq_rightTail
    {ι : Type*} [Fintype ι] (c p : ι → ℝ) {u : ℝ}
    (hu : ∀ i, p i ≤ u) :
    unitExponentialFiniteKernelResponse c p u =
      unitExponentialFiniteKernelTailCharge c p +
        Real.exp (-u / 2) * unitExponentialFiniteKernelTailMode c p := by
  simp only [unitExponentialFiniteKernelResponse,
    unitExponentialFiniteKernelTailCharge, unitExponentialFiniteKernelTailMode,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [unitExponentialIncrementKernel_eq_rightTail (hu i)]
  ring

def unitRieszCoherentPrimeKernelResponse (X : ℝ) (K : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    (ArithmeticFunction.vonMangoldt k / Real.sqrt X) *
      unitExponentialIncrementKernel (Real.log X - Real.log k) u

def unitRieszCoherentPrimeKernelTailMode (X : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    (ArithmeticFunction.vonMangoldt k / Real.sqrt X) *
      (Real.exp ((Real.log X - Real.log k) / 2) - 1)

theorem unitRieszCoherentPrimeKernelTailCharge_eq
    {X : ℝ} {K : ℕ} (hX : 0 < X) (hKX : (K : ℝ) ≤ X) :
    (∑ k ∈ Finset.Icc 2 K,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt X) *
          (1 - Real.exp (-(Real.log X - Real.log k) / 2))) =
      unitRieszCoherentPrimeEnergy X K / 2 := by
  rw [unitRieszCoherentPrimeEnergy, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
  have hkX : (k : ℝ) ≤ X := le_trans (by exact_mod_cast hkK) hKX
  have hlog : Real.log k ≤ Real.log X := Real.strictMonoOn_log.monotoneOn hkpos hX hkX
  have habs : |Real.log X - Real.log k| = Real.log X - Real.log k :=
    abs_of_nonneg (sub_nonneg.mpr hlog)
  rw [unitExponentialCoherentDistanceSq_eq, habs]
  ring

theorem unitRieszCoherentPrimeKernelResponse_eq_rightTail
    {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : Real.log N ≤ u) :
    unitRieszCoherentPrimeKernelResponse N N u =
      unitRieszCoherentPrimeEnergy N N / 2 +
        Real.exp (-u / 2) * unitRieszCoherentPrimeKernelTailMode N N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  unfold unitRieszCoherentPrimeKernelResponse unitRieszCoherentPrimeKernelTailMode
  rw [← unitRieszCoherentPrimeKernelTailCharge_eq hNR (le_refl (N : ℝ)),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by
    have hk1 : 1 ≤ k := by omega
    exact_mod_cast hk1)
  have hlag : Real.log N - Real.log k ≤ u := by linarith
  rw [unitExponentialIncrementKernel_eq_rightTail hlag]
  ring

theorem integral_Ioc_rexp_neg_mul
    {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u) :
    (∫ p in Ioc (0 : ℝ) u, Real.exp (-(b * p))) =
      (1 - Real.exp (-(b * u))) / b := by
  have hwhole := integral_Ioi_rexp_neg_mul_shift hb (0 : ℝ)
  have htail := integral_Ioi_rexp_neg_mul_shift hb u
  have hfirst : IntegrableOn (fun p : ℝ => Real.exp (-(b * p))) (Ioc 0 u) :=
    by simpa only [neg_mul] using
      (exp_neg_integrableOn_Ioi 0 hb).mono_set Ioc_subset_Ioi_self
  have hsecond : IntegrableOn (fun p : ℝ => Real.exp (-(b * p))) (Ioi u) :=
    by simpa only [neg_mul] using exp_neg_integrableOn_Ioi u hb
  have hsplit : Ioi (0 : ℝ) = Ioc 0 u ∪ Ioi u :=
    (Ioc_union_Ioi_eq_Ioi hu).symm
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    hfirst hsecond, htail] at hwhole
  rw [show Real.exp (-(b * (0 : ℝ))) = 1 by simp] at hwhole
  field_simp [hb.ne'] at hwhole ⊢
  linarith

def unitExponentialPolarKernelResponse (u : ℝ) : ℝ :=
  ∫ p in Ioi (0 : ℝ),
    Real.exp (-p) * unitExponentialIncrementKernel p u

theorem unitExponentialPolarKernelResponse_eq
    {u : ℝ} (hu : 0 ≤ u) :
    unitExponentialPolarKernelResponse u =
      1 / 3 + Real.exp (-u / 2) - (4 / 3) * Real.exp (-u) := by
  let f : ℝ → ℝ := fun p => Real.exp (-p) * unitExponentialIncrementKernel p u
  let fL : ℝ → ℝ := fun p =>
    (1 - Real.exp (-u / 2)) * Real.exp (-p) -
      Real.exp (-(3 / 2) * p) +
        Real.exp (-u / 2) * Real.exp (-(1 / 2) * p)
  let fR : ℝ → ℝ := fun p =>
    (1 - Real.exp (-u / 2)) * Real.exp (-p) +
      (Real.exp (u / 2) - 1) * Real.exp (-(3 / 2) * p)
  have hfL : ∀ p ∈ Ioc (0 : ℝ) u, f p = fL p := by
    intro p hp
    dsimp only [f, fL]
    have habs : |p - u| = u - p := by
      rw [abs_of_nonpos (sub_nonpos.mpr hp.2)]
      ring
    rw [unitExponentialIncrementKernel, habs]
    have h1 : Real.exp (-p) * Real.exp (-p / 2) =
        Real.exp (-(3 / 2) * p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-p) * Real.exp (-(u - p) / 2) =
        Real.exp (-u / 2) * Real.exp (-(1 / 2) * p) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (-p) *
          (1 - Real.exp (-p / 2) - Real.exp (-u / 2) + Real.exp (-(u - p) / 2)) =
        (1 - Real.exp (-u / 2)) * Real.exp (-p) -
          Real.exp (-p) * Real.exp (-p / 2) +
            Real.exp (-p) * Real.exp (-(u - p) / 2) := by ring
      _ = _ := by rw [h1, h2]
  have hfR : ∀ p ∈ Ioi u, f p = fR p := by
    intro p hp
    dsimp only [f, fR]
    have habs : |p - u| = p - u := abs_of_pos (sub_pos.mpr hp)
    rw [unitExponentialIncrementKernel, habs]
    have h1 : Real.exp (-p) * Real.exp (-p / 2) =
        Real.exp (-(3 / 2) * p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-p) * Real.exp (-(p - u) / 2) =
        Real.exp (u / 2) * Real.exp (-(3 / 2) * p) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (-p) *
          (1 - Real.exp (-p / 2) - Real.exp (-u / 2) + Real.exp (-(p - u) / 2)) =
        (1 - Real.exp (-u / 2)) * Real.exp (-p) -
          Real.exp (-p) * Real.exp (-p / 2) +
            Real.exp (-p) * Real.exp (-(p - u) / 2) := by ring
      _ = _ := by rw [h1, h2]; ring
  have hIoc1 : IntegrableOn (fun p : ℝ => Real.exp (-p)) (Ioc 0 u) :=
    by
      convert (exp_neg_integrableOn_Ioi 0 one_pos).mono_set Ioc_subset_Ioi_self using 1 <;>
        ring
  have hIoc3 : IntegrableOn (fun p : ℝ => Real.exp (-(3 / 2) * p)) (Ioc 0 u) :=
    (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 3 / 2)).mono_set
      Ioc_subset_Ioi_self
  have hIocHalf : IntegrableOn (fun p : ℝ => Real.exp (-(1 / 2) * p)) (Ioc 0 u) :=
    (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).mono_set
      Ioc_subset_Ioi_self
  have hIoi1 : IntegrableOn (fun p : ℝ => Real.exp (-p)) (Ioi u) := by
    convert exp_neg_integrableOn_Ioi u one_pos using 1 <;> ring
  have hIoi3 : IntegrableOn (fun p : ℝ => Real.exp (-(3 / 2) * p)) (Ioi u) :=
    exp_neg_integrableOn_Ioi u (by norm_num : (0 : ℝ) < 3 / 2)
  have hintL : IntegrableOn fL (Ioc 0 u) := by
    dsimp only [fL]
    exact ((hIoc1.const_mul _).sub hIoc3).add (hIocHalf.const_mul _)
  have hintR : IntegrableOn fR (Ioi u) := by
    dsimp only [fR]
    exact (hIoi1.const_mul _).add (hIoi3.const_mul _)
  have hintfL : IntegrableOn f (Ioc 0 u) :=
    hintL.congr_fun (fun p hp => (hfL p hp).symm) measurableSet_Ioc
  have hintfR : IntegrableOn f (Ioi u) :=
    hintR.congr_fun (fun p hp => (hfR p hp).symm) measurableSet_Ioi
  have hs : Ioi (0 : ℝ) = Ioc 0 u ∪ Ioi u := (Ioc_union_Ioi_eq_Ioi hu).symm
  have hleft : (∫ p in Ioc (0 : ℝ) u, f p) =
      (1 - Real.exp (-u / 2)) * (1 - Real.exp (-u)) -
        (1 - Real.exp (-(3 / 2) * u)) / (3 / 2) +
          Real.exp (-u / 2) *
            ((1 - Real.exp (-(1 / 2) * u)) / (1 / 2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hfL]
    dsimp only [fL]
    have hJ1 : (∫ p in Ioc (0 : ℝ) u, Real.exp (-p)) =
        1 - Real.exp (-u) := by
      convert integral_Ioc_rexp_neg_mul one_pos hu using 1 <;> ring
    have hJ3 : (∫ p in Ioc (0 : ℝ) u, Real.exp (-(3 / 2) * p)) =
        (1 - Real.exp (-(3 / 2) * u)) / (3 / 2) := by
      convert integral_Ioc_rexp_neg_mul (by norm_num : (0 : ℝ) < 3 / 2) hu using 1 <;>
        ring
    have hJh : (∫ p in Ioc (0 : ℝ) u, Real.exp (-(1 / 2) * p)) =
        (1 - Real.exp (-(1 / 2) * u)) / (1 / 2) := by
      convert integral_Ioc_rexp_neg_mul (by norm_num : (0 : ℝ) < 1 / 2) hu using 1 <;>
        ring
    have hadd :
        (∫ p in Ioc (0 : ℝ) u,
            ((1 - Real.exp (-u / 2)) * Real.exp (-p) - Real.exp (-(3 / 2) * p)) +
              Real.exp (-u / 2) * Real.exp (-(1 / 2) * p)) =
          (∫ p in Ioc (0 : ℝ) u,
            (1 - Real.exp (-u / 2)) * Real.exp (-p) - Real.exp (-(3 / 2) * p)) +
          ∫ p in Ioc (0 : ℝ) u,
            Real.exp (-u / 2) * Real.exp (-(1 / 2) * p) :=
      integral_add ((hIoc1.const_mul _).sub hIoc3) (hIocHalf.const_mul _)
    have hsub :
        (∫ p in Ioc (0 : ℝ) u,
            (1 - Real.exp (-u / 2)) * Real.exp (-p) - Real.exp (-(3 / 2) * p)) =
          (∫ p in Ioc (0 : ℝ) u,
            (1 - Real.exp (-u / 2)) * Real.exp (-p)) -
          ∫ p in Ioc (0 : ℝ) u, Real.exp (-(3 / 2) * p) :=
      integral_sub (hIoc1.const_mul _) hIoc3
    have hmul1 :
        (∫ p in Ioc (0 : ℝ) u,
            (1 - Real.exp (-u / 2)) * Real.exp (-p)) =
          (1 - Real.exp (-u / 2)) * ∫ p in Ioc (0 : ℝ) u, Real.exp (-p) :=
      integral_const_mul (μ := volume.restrict (Ioc (0 : ℝ) u))
        (1 - Real.exp (-u / 2)) (fun p : ℝ => Real.exp (-p))
    have hmulh :
        (∫ p in Ioc (0 : ℝ) u,
            Real.exp (-u / 2) * Real.exp (-(1 / 2) * p)) =
          Real.exp (-u / 2) * ∫ p in Ioc (0 : ℝ) u, Real.exp (-(1 / 2) * p) :=
      integral_const_mul (μ := volume.restrict (Ioc (0 : ℝ) u))
        (Real.exp (-u / 2)) (fun p : ℝ => Real.exp (-(1 / 2) * p))
    calc
      (∫ p in Ioc (0 : ℝ) u,
          (1 - Real.exp (-u / 2)) * Real.exp (-p) - Real.exp (-(3 / 2) * p) +
            Real.exp (-u / 2) * Real.exp (-(1 / 2) * p)) =
        (1 - Real.exp (-u / 2)) * (∫ p in Ioc (0 : ℝ) u, Real.exp (-p)) -
          (∫ p in Ioc (0 : ℝ) u, Real.exp (-(3 / 2) * p)) +
          Real.exp (-u / 2) * (∫ p in Ioc (0 : ℝ) u, Real.exp (-(1 / 2) * p)) := by
            rw [hadd, hsub, hmul1, hmulh]
      _ = _ := by rw [hJ1, hJ3, hJh]
  have hright : (∫ p in Ioi u, f p) =
      (1 - Real.exp (-u / 2)) * Real.exp (-u) +
        (Real.exp (u / 2) - 1) *
          (Real.exp (-(3 / 2) * u) / (3 / 2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hfR]
    dsimp only [fR]
    have ht1 : (∫ p in Ioi u, Real.exp (-p)) = Real.exp (-u) := by
      convert integral_Ioi_rexp_neg_mul_shift one_pos u using 1 <;> ring
    have ht3 : (∫ p in Ioi u, Real.exp (-(3 / 2) * p)) =
        Real.exp (-(3 / 2) * u) / (3 / 2) := by
      convert integral_Ioi_rexp_neg_mul_shift (by norm_num : (0 : ℝ) < 3 / 2) u using 1 <;>
        ring
    calc
      (∫ p in Ioi u,
          (1 - Real.exp (-u / 2)) * Real.exp (-p) +
            (Real.exp (u / 2) - 1) * Real.exp (-(3 / 2) * p)) =
        (1 - Real.exp (-u / 2)) * (∫ p in Ioi u, Real.exp (-p)) +
          (Real.exp (u / 2) - 1) * (∫ p in Ioi u, Real.exp (-(3 / 2) * p)) := by
            rw [integral_add (hIoi1.const_mul _) (hIoi3.const_mul _),
              integral_const_mul, integral_const_mul]
      _ = _ := by rw [ht1, ht3]
  unfold unitExponentialPolarKernelResponse
  change (∫ p in Ioi (0 : ℝ), f p) = _
  rw [hs, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hintfL hintfR,
    hleft, hright]
  have e2 : Real.exp (-u) = Real.exp (-u / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have e3 : Real.exp (-(3 / 2) * u) = Real.exp (-u / 2) ^ 3 := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ep : Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have ep3 : Real.exp (u / 2) * Real.exp (-u / 2) ^ 3 =
      Real.exp (-u / 2) ^ 2 := by
    calc
      _ = (Real.exp (u / 2) * Real.exp (-u / 2)) *
          Real.exp (-u / 2) ^ 2 := by ring
      _ = _ := by rw [ep]; ring
  rw [e2, e3]
  field_simp
  ring_nf at ep3 ⊢
  rw [ep3]
  ring

def unitRieszCoherentPolarKernelResponse (X u : ℝ) : ℝ :=
  Real.sqrt X * unitExponentialPolarKernelResponse u

theorem unitRieszCoherentPolarKernelResponse_eq
    {X u : ℝ} (hu : 0 ≤ u) :
    unitRieszCoherentPolarKernelResponse X u =
      Real.sqrt X *
        (1 / 3 + Real.exp (-u / 2) - (4 / 3) * Real.exp (-u)) := by
  rw [unitRieszCoherentPolarKernelResponse, unitExponentialPolarKernelResponse_eq hu]

def unitRieszCoherentCompletedKernelResponse (N : ℕ) (u : ℝ) : ℝ :=
  unitRieszCoherentPrimeKernelResponse N N u -
    unitRieszCoherentPolarKernelResponse N u

theorem unitRieszCoherentCompletedKernelResponse_eq_rightTail
    {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : Real.log N ≤ u) :
    unitRieszCoherentCompletedKernelResponse N u =
      criticalMellinChebyshevResolventSource (Real.log N) / 2 +
        Real.exp (-u / 2) *
          (unitRieszCoherentPrimeKernelTailMode N N - Real.sqrt N) +
        (4 / 3) * Real.sqrt N * Real.exp (-u) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by
    have hN1 : 1 ≤ N := by omega
    exact_mod_cast hN1)
  rw [unitRieszCoherentCompletedKernelResponse,
    unitRieszCoherentPrimeKernelResponse_eq_rightTail hN hu,
    unitRieszCoherentPolarKernelResponse_eq (le_trans hlogN hu),
    criticalMellinChebyshevResolventSource_log_nat_eq_coherentPrime_sub_polar
      (by omega : 1 ≤ N),
    unitRieszCoherentPolarEnergy_eq
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN) : (0 : ℝ) < N)]
  ring

theorem tendsto_unitRieszCoherentCompletedKernelResponse
    {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (unitRieszCoherentCompletedKernelResponse N) atTop
      (𝓝 (criticalMellinChebyshevResolventSource (Real.log N) / 2)) := by
  have hexpHalf : Tendsto (fun u : ℝ => Real.exp (-u / 2)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun u : ℝ => -u / 2) atTop atBot := by
      have h := tendsto_id.const_mul_atTop_of_neg
        (by norm_num : (-1 / 2 : ℝ) < 0)
      convert h using 1
      funext u
      simp only [id_eq]
      ring
    exact Real.tendsto_exp_atBot.comp hlin
  have hexp : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun u : ℝ => -u) atTop atBot := tendsto_neg_atTop_atBot
    exact Real.tendsto_exp_atBot.comp hlin
  have hformula : Tendsto (fun u : ℝ =>
      criticalMellinChebyshevResolventSource (Real.log N) / 2 +
        Real.exp (-u / 2) *
          (unitRieszCoherentPrimeKernelTailMode N N - Real.sqrt N) +
        (4 / 3) * Real.sqrt N * Real.exp (-u)) atTop
      (𝓝 (criticalMellinChebyshevResolventSource (Real.log N) / 2)) := by
    simpa using
      ((tendsto_const_nhds.add
        (hexpHalf.mul_const
          (unitRieszCoherentPrimeKernelTailMode N N - Real.sqrt N))).add
        (hexp.const_mul ((4 / 3) * Real.sqrt N)))
  refine hformula.congr' ?_
  filter_upwards [eventually_ge_atTop (Real.log N)] with u hu
  exact (unitRieszCoherentCompletedKernelResponse_eq_rightTail hN hu).symm

theorem tendsto_unitRieszCoherentCompletedKernelResponse_zero_iff
    {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (unitRieszCoherentCompletedKernelResponse N) atTop (𝓝 0) ↔
      criticalMellinChebyshevResolventSource (Real.log N) = 0 := by
  have hlim := tendsto_unitRieszCoherentCompletedKernelResponse hN
  constructor
  · intro hzero
    have heq : (0 : ℝ) = criticalMellinChebyshevResolventSource (Real.log N) / 2 :=
      tendsto_nhds_unique hzero hlim
    linarith
  · intro hzero
    simpa [hzero] using hlim

theorem not_integrableOn_sq_of_tendsto_atTop_ne_zero
    {f : ℝ → ℝ} {c : ℝ} (hlim : Tendsto f atTop (𝓝 c)) (hc : c ≠ 0) (a : ℝ) :
    ¬ IntegrableOn (fun u => f u ^ 2) (Ioi a) := by
  intro hint
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hsq : Tendsto (fun u => f u ^ 2) atTop (𝓝 (c ^ 2)) := hlim.pow 2
  have hev : ∀ᶠ u in atTop, c ^ 2 / 2 < f u ^ 2 :=
    (tendsto_order.1 hsq).1 (c ^ 2 / 2) (by linarith)
  obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
  set M : ℝ := max N a with hM
  have hsub : IntegrableOn (fun u => f u ^ 2) (Ioi M) :=
    hint.mono_set (Ioi_subset_Ioi (le_max_right N a))
  have hle : ∀ u ∈ Ioi M,
      ENNReal.ofReal (c ^ 2 / 2) ≤ ‖f u ^ 2‖ₑ := by
    intro u hu
    have huLower : c ^ 2 / 2 < f u ^ 2 :=
      hN u (le_trans (le_max_left N a) hu.le)
    have hreal : c ^ 2 / 2 ≤ ‖f u ^ 2‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f u))]
      exact huLower.le
    calc
      ENNReal.ofReal (c ^ 2 / 2) ≤ ENNReal.ofReal ‖f u ^ 2‖ :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ‖f u ^ 2‖ₑ := ofReal_norm _
  have hconst : (∫⁻ _u in Ioi M, ENNReal.ofReal (c ^ 2 / 2)) = ⊤ := by
    rw [setLIntegral_const, Real.volume_Ioi]
    have hne : ENNReal.ofReal (c ^ 2 / 2) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le.mpr (by positivity : 0 < c ^ 2 / 2)]
    simp [hne]
  have hlint : (∫⁻ u in Ioi M, ‖f u ^ 2‖ₑ) = ⊤ := by
    have hmono : (∫⁻ _u in Ioi M, ENNReal.ofReal (c ^ 2 / 2)) ≤
        ∫⁻ u in Ioi M, ‖f u ^ 2‖ₑ := by
      apply setLIntegral_mono' measurableSet_Ioi
      exact hle
    rw [hconst] at hmono
    exact top_le_iff.mp hmono
  have hfinite := hsub.2
  rw [HasFiniteIntegral, hlint] at hfinite
  exact absurd hfinite (by simp)

theorem not_integrableOn_sq_unitRieszCoherentCompletedKernelResponse
    {N : ℕ} (hN : 2 ≤ N)
    (hres : criticalMellinChebyshevResolventSource (Real.log N) ≠ 0) :
    ¬ IntegrableOn (fun u => unitRieszCoherentCompletedKernelResponse N u ^ 2)
      (Ioi (0 : ℝ)) := by
  apply not_integrableOn_sq_of_tendsto_atTop_ne_zero
    (tendsto_unitRieszCoherentCompletedKernelResponse hN)
  exact div_ne_zero hres (by norm_num)

def unitRieszCoherentCompletedAmplitudeProfile (N : ℕ) (u : ℝ) : ℂ :=
  (unitRieszCoherentCompletedKernelResponse N u : ℝ)

theorem leakDensity_unitRieszCoherentCompletedAmplitudeProfile (N : ℕ) (u : ℝ) :
    leakDensity (unitRieszCoherentCompletedAmplitudeProfile N) u =
      unitRieszCoherentCompletedKernelResponse N u ^ 2 := by
  rw [leakDensity, unitRieszCoherentCompletedAmplitudeProfile, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Direct HG use of literal completed coherent response fails exactly away from zero resolvent:
its arithmetic tail charge makes amplitude leakage nonintegrable. -/
theorem not_leakProfile_unitRieszCoherentCompletedAmplitudeProfile
    {N : ℕ} (hN : 2 ≤ N)
    (hres : criticalMellinChebyshevResolventSource (Real.log N) ≠ 0) :
    ¬ LeakProfile (unitRieszCoherentCompletedAmplitudeProfile N) := by
  intro hp
  have hint := hp.integrable
  have hintSq : IntegrableOn
      (fun u => unitRieszCoherentCompletedKernelResponse N u ^ 2) (Ioi (0 : ℝ)) := by
    refine hint.congr_fun ?_ measurableSet_Ioi
    intro u _hu
    exact leakDensity_unitRieszCoherentCompletedAmplitudeProfile N u
  exact not_integrableOn_sq_unitRieszCoherentCompletedKernelResponse hN hres hintSq

end GaloisForLFunctions.RHTower

