import GaloisForLFunctions.RHTower.CCM.CCMTwoChannelGraph

/-!
# The Euler/Gamma Radon–Nikodym correction and the critical recession

Four exact mechanisms of the card are formalized.

*The Gamma diagonal at a prime power.*  With `φ(t) = (cosh t)^{-1/2}` one has exactly

```text
φ(2 k log p) = √2 · p^k / √(p^{4k} + 1) ,
```

which is `(4)`.

*The Radon–Nikodym correction is a bounded positive contraction.*  Dividing the Euler atom
`w_{p,k} = 1/(k p^k)` by that diagonal gives `√(p^{4k}+1)/(√2 k p^{2k})`, and this lies between
`1/(√2 k)` and `1/k ≤ 1` — equations `(5)`–`(7)`.

*The prime-power tail is absolutely summable.*  For each prime `p`, `∑_{k≥2} 1/(k p^k) ≤ 1/(p(p-1))`
— equation `(10)`.

*The critical correction recedes.*  The diagonal factor matching the von Mangoldt magnitude
`(log p) p^{-k/2}` is at least `(log p) p^{k/2}/√2`, hence unbounded in the prime-power direction —
equations `(14)`–`(16)`.

The Gamma cyclic representation, the Hilbert–Schmidt synthesis `(8)` and the trace identities
`(11)`–`(12)` are cited parents.  The exponential divided-difference kernel `(17)` is already
carried by `CCMTwoChannelGraph.bilateral_atom_factorization`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The two canonical weights -/

/-- The Gamma damping profile `φ(t) = (cosh t)^{-1/2}` of `(1)`. -/
def gammaDampingProfile (t : ℝ) : ℝ := Real.cosh t ^ (-(1 : ℝ) / 2)

/-- The Euler-log atom `w_{p,k} = 1/(k p^k)` of `(1)`–`(2)`. -/
def eulerAtom (p k : ℕ) : ℝ := 1 / (k * (p : ℝ) ^ k)

/-- The Gamma diagonal norm `d_{p,k}² = φ(2 k log p)` of `(1)`. -/
def gammaDiagSq (p k : ℕ) : ℝ := gammaDampingProfile (2 * ((k : ℝ) * Real.log p))

theorem gammaDampingProfile_eq_inv_sqrt (t : ℝ) :
    gammaDampingProfile t = (Real.sqrt (Real.cosh t))⁻¹ := by
  have hpos : 0 < Real.cosh t := Real.cosh_pos t
  rw [gammaDampingProfile, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
    Real.rpow_neg (le_of_lt hpos), Real.sqrt_eq_rpow]

/-- **Equation (4).**  The exact Gamma diagonal at a prime power. -/
theorem gammaDiagSq_eq {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    gammaDiagSq p k
      = Real.sqrt 2 * (p : ℝ) ^ k / Real.sqrt ((p : ℝ) ^ (4 * k) + 1) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have hp0 : (0 : ℕ) < p := by omega
    exact_mod_cast hp0
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hppos k
  have hp2k : (0 : ℝ) < (p : ℝ) ^ (2 * k) := pow_pos hppos (2 * k)
  have hexp : Real.exp (2 * ((k : ℝ) * Real.log p)) = (p : ℝ) ^ (2 * k) := by
    have hcast : 2 * ((k : ℝ) * Real.log p) = ((2 * k : ℕ) : ℝ) * Real.log p := by
      push_cast; ring
    rw [hcast, Real.exp_nat_mul, Real.exp_log hppos]
  have h4 : (p : ℝ) ^ (4 * k) = ((p : ℝ) ^ (2 * k)) ^ 2 := by
    rw [← pow_mul]
    ring_nf
  have hcosh : Real.cosh (2 * ((k : ℝ) * Real.log p))
      = ((p : ℝ) ^ (4 * k) + 1) / (2 * (p : ℝ) ^ (2 * k)) := by
    rw [Real.cosh_eq, hexp, Real.exp_neg, hexp, h4]
    field_simp
  have hnum : (0 : ℝ) ≤ (p : ℝ) ^ (4 * k) + 1 := by positivity
  have hsq2k : Real.sqrt ((p : ℝ) ^ (2 * k)) = (p : ℝ) ^ k := by
    have hrw : (p : ℝ) ^ (2 * k) = ((p : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul]
      ring_nf
    rw [hrw, Real.sqrt_sq (le_of_lt hpk)]
  rw [gammaDiagSq, gammaDampingProfile_eq_inv_sqrt, hcosh, Real.sqrt_div hnum, inv_div,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hsq2k]

/-! ## The Radon–Nikodym correction -/

/-- The Radon–Nikodym correction `r_{p,k} = w_{p,k}/d_{p,k}²` of `(3)`. -/
def radonNikodym (p k : ℕ) : ℝ := eulerAtom p k / gammaDiagSq p k

/-- **Equation (5).**  The exact Radon–Nikodym correction. -/
theorem radonNikodym_eq {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    radonNikodym p k
      = Real.sqrt ((p : ℝ) ^ (4 * k) + 1) / (Real.sqrt 2 * (k : ℝ) * (p : ℝ) ^ (2 * k)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have hp0 : (0 : ℕ) < p := by omega
    exact_mod_cast hp0
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hppos k
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℕ) < k := by omega
    exact_mod_cast this
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsnum : (0 : ℝ) < Real.sqrt ((p : ℝ) ^ (4 * k) + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  have hpow : (p : ℝ) ^ (2 * k) = (p : ℝ) ^ k * (p : ℝ) ^ k := by
    rw [← pow_add]
    ring_nf
  rw [radonNikodym, gammaDiagSq_eq hp, eulerAtom, hpow]
  field_simp

/-- **Equation (6), lower bound.** -/
theorem radonNikodym_lower {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    1 / (Real.sqrt 2 * (k : ℝ)) ≤ radonNikodym p k := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have hp0 : (0 : ℕ) < p := by omega
    exact_mod_cast hp0
  have hp2k : (0 : ℝ) < (p : ℝ) ^ (2 * k) := pow_pos hppos (2 * k)
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℕ) < k := by omega
    exact_mod_cast this
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h4 : (p : ℝ) ^ (4 * k) = ((p : ℝ) ^ (2 * k)) ^ 2 := by
    rw [← pow_mul]
    ring_nf
  have hge : (p : ℝ) ^ (2 * k) ≤ Real.sqrt ((p : ℝ) ^ (4 * k) + 1) := by
    rw [show (p : ℝ) ^ (2 * k) = Real.sqrt (((p : ℝ) ^ (2 * k)) ^ 2) from
      (Real.sqrt_sq (le_of_lt hp2k)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [← h4]
    linarith
  have h1 : (0 : ℝ) < Real.sqrt 2 * (k : ℝ) := by positivity
  rw [radonNikodym_eq hp hk, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hge (le_of_lt h1)]

/-- **Equation (6), upper bound.** -/
theorem radonNikodym_upper {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    radonNikodym p k ≤ 1 / (k : ℝ) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have hp0 : (0 : ℕ) < p := by omega
    exact_mod_cast hp0
  have hp2k : (0 : ℝ) < (p : ℝ) ^ (2 * k) := pow_pos hppos (2 * k)
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℕ) < k := by omega
    exact_mod_cast this
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h4 : (p : ℝ) ^ (4 * k) = ((p : ℝ) ^ (2 * k)) ^ 2 := by
    rw [← pow_mul]
    ring_nf
  have hone : (1 : ℝ) ≤ (p : ℝ) ^ (4 * k) := by
    refine one_le_pow₀ ?_
    have : (1 : ℕ) ≤ p := by omega
    exact_mod_cast this
  have hle : Real.sqrt ((p : ℝ) ^ (4 * k) + 1) ≤ Real.sqrt 2 * (p : ℝ) ^ (2 * k) := by
    have hrhs : Real.sqrt 2 * (p : ℝ) ^ (2 * k)
        = Real.sqrt (2 * ((p : ℝ) ^ (2 * k)) ^ 2) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (le_of_lt hp2k)]
    rw [hrhs]
    refine Real.sqrt_le_sqrt ?_
    rw [← h4]
    linarith
  rw [radonNikodym_eq hp hk, div_le_div_iff₀ (by positivity) hkpos]
  nlinarith [mul_le_mul_of_nonneg_right hle (le_of_lt hkpos)]

/-- **Equation (7).**  The correction is exactly the one matching the Euler atom. -/
theorem radonNikodym_mul_gammaDiagSq {p k : ℕ} (hp : 2 ≤ p) :
    radonNikodym p k * gammaDiagSq p k = eulerAtom p k := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have hp0 : (0 : ℕ) < p := by omega
    exact_mod_cast hp0
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hppos k
  have hsnum : (0 : ℝ) < Real.sqrt ((p : ℝ) ^ (4 * k) + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hd : gammaDiagSq p k ≠ 0 := by
    rw [gammaDiagSq_eq hp]
    positivity
  rw [radonNikodym, div_mul_cancel₀ _ hd]

/-! ## The prime-power tail -/

/-- **Equation (10).**  For each prime the deep prime-power tail is bounded by `1/(p(p-1))`. -/
theorem tsum_eulerAtom_tail_le {p : ℕ} (hp : 2 ≤ p) :
    ∑' k : ℕ, eulerAtom p (k + 2) ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have hp0 : (0 : ℕ) < p := by omega
    exact_mod_cast hp0
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hinv : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := le_of_lt (inv_pos.mpr hppos)
  have hlt : ((p : ℝ))⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right; linarith
  have hgeo : HasSum (fun k : ℕ => ((p : ℝ))⁻¹ ^ k) (1 - ((p : ℝ))⁻¹)⁻¹ :=
    hasSum_geometric_of_lt_one hinv hlt
  have hsummable : Summable (fun k : ℕ => ((p : ℝ))⁻¹ ^ (k + 2)) := by
    refine (hgeo.summable.mul_left (((p : ℝ))⁻¹ ^ 2)).congr fun k => ?_
    rw [pow_add]
    ring
  have hterm : ∀ k : ℕ, eulerAtom p (k + 2) ≤ ((p : ℝ))⁻¹ ^ (k + 2) := by
    intro k
    have hpk : (0 : ℝ) < (p : ℝ) ^ (k + 2) := pow_pos hppos _
    have hk1 : (1 : ℝ) ≤ ((k : ℝ) + 2) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [eulerAtom, inv_pow, ← one_div]
    have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [hcast, div_le_div_iff₀ (by positivity) hpk]
    nlinarith [hpk, hk1]
  have hnonneg : ∀ k : ℕ, 0 ≤ eulerAtom p (k + 2) := by
    intro k
    rw [eulerAtom]
    positivity
  have hsummable' : Summable (fun k : ℕ => eulerAtom p (k + 2)) :=
    Summable.of_nonneg_of_le hnonneg hterm hsummable
  have hsum : ∑' k : ℕ, eulerAtom p (k + 2) ≤ ∑' k : ℕ, ((p : ℝ))⁻¹ ^ (k + 2) :=
    Summable.tsum_mono hsummable' hsummable hterm
  refine le_trans hsum ?_
  have hval : ∑' k : ℕ, ((p : ℝ))⁻¹ ^ (k + 2) = ((p : ℝ))⁻¹ ^ 2 * (1 - ((p : ℝ))⁻¹)⁻¹ := by
    rw [← hgeo.tsum_eq, ← tsum_mul_left]
    exact tsum_congr fun k => by rw [pow_add]; ring
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hgeoval : (1 : ℝ) - ((p : ℝ))⁻¹ = ((p : ℝ) - 1) / (p : ℝ) := by
    field_simp
  have heq : ((p : ℝ))⁻¹ ^ 2 * (1 - ((p : ℝ))⁻¹)⁻¹ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [hgeoval]
    field_simp
  rw [hval, heq]

/-! ## The critical recession -/

/-- The critical von Mangoldt magnitude `(log p) p^{-k/2}` of `(13)`. -/
def vonMangoldtMagnitude (p k : ℕ) : ℝ := Real.log p / Real.sqrt ((p : ℝ) ^ k)

/-- The diagonal factor `(14)` matching the critical magnitude. -/
def criticalCorrection (p k : ℕ) : ℝ := vonMangoldtMagnitude p k / gammaDiagSq p k

/-- **Equation (15).**  The critical correction is at least `(log p) p^{k/2}/√2`. -/
theorem criticalCorrection_lower {p k : ℕ} (hp : 2 ≤ p) :
    Real.log p * Real.sqrt ((p : ℝ) ^ k) / Real.sqrt 2 ≤ criticalCorrection p k := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have hp0 : (0 : ℕ) < p := by omega
    exact_mod_cast hp0
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hppos k
  have hp2k : (0 : ℝ) < (p : ℝ) ^ (2 * k) := pow_pos hppos (2 * k)
  have hspk : (0 : ℝ) < Real.sqrt ((p : ℝ) ^ k) := Real.sqrt_pos.mpr hpk
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlog : (0 : ℝ) < Real.log p := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h4 : (p : ℝ) ^ (4 * k) = ((p : ℝ) ^ (2 * k)) ^ 2 := by
    rw [← pow_mul]
    ring_nf
  have hge : (p : ℝ) ^ (2 * k) ≤ Real.sqrt ((p : ℝ) ^ (4 * k) + 1) := by
    rw [show (p : ℝ) ^ (2 * k) = Real.sqrt (((p : ℝ) ^ (2 * k)) ^ 2) from
      (Real.sqrt_sq (le_of_lt hp2k)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [← h4]
    linarith
  have hsq : Real.sqrt ((p : ℝ) ^ k) * Real.sqrt ((p : ℝ) ^ k) = (p : ℝ) ^ k :=
    Real.mul_self_sqrt (le_of_lt hpk)
  have hpow : (p : ℝ) ^ (2 * k) = (p : ℝ) ^ k * (p : ℝ) ^ k := by
    rw [← pow_add]
    ring_nf
  have hrhs : criticalCorrection p k
      = Real.log p * Real.sqrt ((p : ℝ) ^ (4 * k) + 1)
        / (Real.sqrt 2 * Real.sqrt ((p : ℝ) ^ k) * (p : ℝ) ^ k) := by
    rw [criticalCorrection, vonMangoldtMagnitude, gammaDiagSq_eq hp]
    field_simp
  rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : Real.log p * Real.sqrt ((p : ℝ) ^ k)
        * (Real.sqrt 2 * Real.sqrt ((p : ℝ) ^ k) * (p : ℝ) ^ k)
      = Real.log p * Real.sqrt 2 * ((p : ℝ) ^ k * (p : ℝ) ^ k) := by
    rw [show Real.log p * Real.sqrt ((p : ℝ) ^ k)
          * (Real.sqrt 2 * Real.sqrt ((p : ℝ) ^ k) * (p : ℝ) ^ k)
        = Real.log p * Real.sqrt 2
          * ((Real.sqrt ((p : ℝ) ^ k) * Real.sqrt ((p : ℝ) ^ k)) * (p : ℝ) ^ k) by ring, hsq]
  rw [hkey, ← hpow]
  nlinarith [mul_le_mul_of_nonneg_left hge (le_of_lt (mul_pos hlog hs2))]


/-- **Equation (16).**  The critical correction is cofinally unbounded in the prime-power
direction: no bounded diagonal renormalization of the Gamma frame reaches the critical source. -/
theorem criticalCorrection_unbounded {p : ℕ} (hp : 2 ≤ p) (M : ℝ) :
    ∃ k : ℕ, M < criticalCorrection p k := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have : (1 : ℕ) < p := by omega
    exact_mod_cast this
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set c : ℝ := Real.sqrt 2 * max M 0 / Real.log p with hc
  have hmax0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hcnn : 0 ≤ c := by
    rw [hc]
    positivity
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (c ^ 2) hp1
  refine ⟨k, ?_⟩
  have hlb := criticalCorrection_lower (p := p) (k := k) hp
  have hsq : c < Real.sqrt ((p : ℝ) ^ k) := by
    have hlt : Real.sqrt (c ^ 2) < Real.sqrt ((p : ℝ) ^ k) :=
      Real.sqrt_lt_sqrt (by positivity) hk
    rwa [Real.sqrt_sq hcnn] at hlt
  have hmax : max M 0 = Real.log p * c / Real.sqrt 2 := by
    rw [hc]
    field_simp
  have h1 : Real.log p * c < Real.log p * Real.sqrt ((p : ℝ) ^ k) :=
    mul_lt_mul_of_pos_left hsq hlog
  have hlt2 : Real.log p * c / Real.sqrt 2
      < Real.log p * Real.sqrt ((p : ℝ) ^ k) / Real.sqrt 2 := by
    have h2 := mul_lt_mul_of_pos_right h1 (inv_pos.mpr hs2)
    simpa [div_eq_mul_inv] using h2
  calc M ≤ max M 0 := le_max_left _ _
    _ = Real.log p * c / Real.sqrt 2 := hmax
    _ < Real.log p * Real.sqrt ((p : ℝ) ^ k) / Real.sqrt 2 := hlt2
    _ ≤ criticalCorrection p k := hlb

end GaloisForLFunctions.RHTower

end
