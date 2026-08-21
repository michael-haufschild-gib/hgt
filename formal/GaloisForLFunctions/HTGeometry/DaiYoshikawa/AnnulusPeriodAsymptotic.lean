import GaloisForLFunctions.HTGeometry.DaiYoshikawa.AnnulusPeriodSubstitution

/-!
# Proposition 5.1 (1): the period integral is a logarithm plus a convergent remainder

For the substitution `y = t/x` on the vanishing annulus the Laurent coefficient at exponent `k` is
`c_k(t) = Σ_{m−n=k} a_{mn} t^n`.  When `k < 0` every fibre exponent satisfies `n ≥ −k`, so `c_k` is
divisible by `t^{−k}`; that divisibility is exactly what cancels the divergent factor `|t|^{2k}`
coming from the radial integral.  Consequently every exponent other than `k = 0` contributes a
*convergent* term, while `k = 0` contributes `2π c₀ \overline{d₀} log|t|^{-1}`.

This is Proposition 5.1 (1) of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small
eigenvalues of the Laplacian* (arXiv:2509.06151v2): the period integral equals
`a_{ij} log|t|^{-2} + b_{ij} + o(1)`, with `a_{ij}` the product of the two residues.
-/

open MeasureTheory Set Real Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

open _root_.HTGeometry (deningerAnnulus)

/-! ## Divisibility of the Laurent coefficients -/

/-- On the fibre over `k ≤ 0` the second exponent is at least `−k`. -/
theorem le_snd_of_mem_substFiber {S : Finset (ℕ × ℕ)} {k : ℤ} {m : ℕ} (hm : (m : ℤ) = -k)
    {p : ℕ × ℕ} (hp : p ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = k) : m ≤ p.2 := by
  rw [Finset.mem_filter] at hp
  have h := hp.2
  omega

/-- The Laurent coefficient with `t^m` divided out. -/
noncomputable def substTail (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) (k : ℤ) (m : ℕ) (t : ℂ) : ℂ :=
  ∑ p ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = k, a p * t ^ (p.2 - m)

theorem continuous_substTail (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) (k : ℤ) (m : ℕ) :
    Continuous (substTail S a k m) := by
  simp only [substTail]
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_pow _)

/-- **Divisibility.**  For `k ≤ 0` the coefficient `c_k` is `t^{−k}` times a polynomial. -/
theorem substCoeff_eq_pow_mul_substTail (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) {k : ℤ} {m : ℕ}
    (hm : (m : ℤ) = -k) (t : ℂ) :
    substCoeff S a k t = t ^ m * substTail S a k m t := by
  rw [substCoeff, substTail, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hle : m ≤ p.2 := le_snd_of_mem_substFiber hm hp
  rw [← mul_assoc, mul_comm (a p) (t ^ m), mul_assoc, ← pow_add]
  congr 2
  omega

/-! ## Convergence of the individual terms -/

/-- The contribution of an exponent `k > 0`. -/
theorem tendsto_substTerm_pos (S T : Finset (ℕ × ℕ)) (a b : ℕ × ℕ → ℂ) {k : ℤ} (hk : 0 < k) :
    Tendsto (fun t : ℂ => substCoeff S a k t * (starRingEnd ℂ) (substCoeff T b k t)
        * (2 * π * (((1 : ℝ) ^ (2 * k) - (‖t‖ : ℝ) ^ (2 * k)) / (2 * k))))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (substCoeff S a k 0 * (starRingEnd ℂ) (substCoeff T b k 0)
        * (2 * π * ((1 : ℝ) / (2 * k))))) := by
  have hc : Continuous fun t : ℂ => substCoeff S a k t := by
    simp only [substCoeff]
    exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_pow _)
  have hd : Continuous fun t : ℂ => (starRingEnd ℂ) (substCoeff T b k t) := by
    refine Complex.continuous_conj.comp ?_
    simp only [substCoeff]
    exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_pow _)
  have hpow : Tendsto (fun t : ℂ => ((‖t‖ : ℝ) ^ (2 * k) : ℝ)) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have hk' : (2 * k).toNat = 2 * k := by omega
    have hnat : ∀ t : ℂ, ((‖t‖ : ℝ) ^ (2 * k) : ℝ) = (‖t‖ : ℝ) ^ (2 * k).toNat := by
      intro t
      rw [← zpow_natCast, hk']
    simp only [hnat]
    have hn : 0 < (2 * k).toNat := by omega
    refine Tendsto.comp (g := fun r : ℝ => r ^ (2 * k).toNat) ?_ ?_
    · simpa using (continuous_pow (2 * k).toNat).tendsto' 0 0 (zero_pow hn.ne')
    · exact (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds |>.congr'
        (Eventually.of_forall fun _ => rfl) |>.congr_right (by simp)
  have hlim := ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).mul
    ((hd.tendsto 0).mono_left nhdsWithin_le_nhds)
  have hfac : Tendsto (fun t : ℂ =>
      (2 * (π : ℂ) * ((((1 : ℝ) ^ (2 * k) - (‖t‖ : ℝ) ^ (2 * k) : ℝ)) / (2 * (k : ℂ)))))
      (𝓝[≠] (0 : ℂ)) (𝓝 (2 * (π : ℂ) * (((1 : ℝ) : ℂ) / (2 * (k : ℂ))))) := by
    have hone : ((1 : ℝ) ^ (2 * k) : ℝ) = 1 := one_zpow _
    have hcast : Tendsto (fun t : ℂ => (((‖t‖ : ℝ) ^ (2 * k) : ℝ) : ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hpow
    have := (tendsto_const_nhds (x := ((1 : ℝ) : ℂ)) (f := 𝓝[≠] (0 : ℂ))).sub hcast
    simp only [hone, sub_zero] at this ⊢
    exact (this.div_const _).const_mul _
  have := hlim.mul hfac
  refine this.congr fun t => ?_
  push_cast
  ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
