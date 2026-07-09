/-
# Exact finite Euler-product data is divisor-inert on the critical strip

The completed local factor `fePants p s = (1 − p^(−s))(1 − p^(−(1−s)))`, built from the entire
inverse Euler factor `eulerInvFactor p s = 1 − exp(−s·log p)`, is entire, functional-equation- and
Schwarz-symmetric, and **nonvanishing on the open strip `0 < Re s < 1`**: each factor `1 − p^(−w)`
lies strictly inside the unit disc about `1` whenever `Re w > 0`, and both `Re s > 0` and
`Re(1 − s) > 0` hold across the strip.  A finite product `feBundle P s = ∏_{p∈P} fePants p s` over
any finite set of primes inherits all three properties.

Consequently multiplying any member of the FE + Schwarz class by `feBundle P` changes **no**
vanishing order at any strip point: `ord_ρ (feBundle P · G) = ord_ρ G` for `0 < Re ρ < 1`.  The
finite-Euler-decorated class `FiniteEulerClass P` — members of the form `feBundle P · G` with `G`
FE + Schwarz — is therefore exactly as soft as the bare class: at every off-line, off-real point it
plants a member of nontrivial deck charge (`finiteEulerClass_isSoft`), so it cannot force RH-grade
parity (`finiteEulerClass_not_forcesRHParity`).  Every finite set of exact local Euler factors
coexists with every strip divisor of the FE + Schwarz class; finite exact germ data carries no
divisor constraint.

Together with the asymptotic blindness of the logarithmic-derivative tail, this pins any
divisor-constraining content of the Euler germ not to any finite truncation but to the exact
infinite product as a whole.
-/
import GaloisForLFunctions.RHTower.GoldilocksTrichotomy
import GaloisForLFunctions.RHTower.SymmetricDivisorRealization

noncomputable section

namespace RHTower

open Complex

/-! ### §1 The entire inverse local Euler factor -/

/-- The entire inverse local Euler factor `1 − exp(−s·log p)`, equal to `1 − p^(−s)` for `p ≥ 1`.
Writing it through `exp` rather than `cpow` makes it manifestly entire. -/
def eulerInvFactor (p : ℕ) (s : ℂ) : ℂ := 1 - Complex.exp (-(s * (Real.log p : ℂ)))

/-- The inverse factor is entire: a constant minus the exponential of a linear map. -/
theorem eulerInvFactor_differentiable (p : ℕ) : Differentiable ℂ (eulerInvFactor p) := by
  unfold eulerInvFactor; fun_prop

/-- The inverse factor is Schwarz-equivariant `f(s̄) = \overline{f(s)}`: the exponent's coefficient
`log p` is real, so `exp` commutes with conjugation. -/
theorem eulerInvFactor_conj (p : ℕ) (s : ℂ) :
    eulerInvFactor p ((starRingEnd ℂ) s) = (starRingEnd ℂ) (eulerInvFactor p s) := by
  simp only [eulerInvFactor, map_sub, map_one]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal]

/-- **The inverse factor is zero-free on the right half-plane.**  For `Re s > 0` and `p > 1` one has
`‖exp(−s·log p)‖ = exp(−Re s·log p) < 1`, so `exp(−s·log p) ≠ 1` and `1 − exp(−s·log p) ≠ 0`. -/
theorem eulerInvFactor_ne_zero (p : ℕ) (hp : 1 < p) {s : ℂ} (hs : 0 < s.re) :
    eulerInvFactor p s ≠ 0 := by
  intro h
  simp only [eulerInvFactor] at h
  have hE : Complex.exp (-(s * (Real.log p : ℂ))) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖Complex.exp (-(s * (Real.log p : ℂ)))‖ = 1 := by rw [hE, norm_one]
  rw [Complex.norm_exp] at hnorm
  have hre : (-(s * (Real.log p : ℂ))).re = -(s.re * Real.log p) := by
    rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre] at hnorm
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hlt : Real.exp (-(s.re * Real.log p)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < s.re * Real.log p := mul_pos hs hL
    linarith
  exact absurd hnorm (ne_of_lt hlt)

/-! ### §2 The FE-completed local factor -/

/-- The FE-completed local Euler factor `(1 − p^(−s))·(1 − p^(−(1−s)))`: the local factor times its
functional-equation mirror.  Entire, and symmetric under `s ↦ 1−s`. -/
def fePants (p : ℕ) (s : ℂ) : ℂ := eulerInvFactor p s * eulerInvFactor p (1 - s)

/-- The completed local factor is entire. -/
theorem fePants_differentiable (p : ℕ) : Differentiable ℂ (fePants p) := by
  have h1 : Differentiable ℂ (fun s : ℂ => eulerInvFactor p (1 - s)) :=
    (eulerInvFactor_differentiable p).comp (by fun_prop)
  exact (eulerInvFactor_differentiable p).mul h1

/-- The completed local factor is FE + Schwarz: substituting `1 − s` swaps the two mirror factors,
and Schwarz equivariance passes through each factor and through `s ↦ 1 − s`. -/
theorem fePants_fESchwarz (p : ℕ) : FESchwarz (fePants p) := by
  refine ⟨fePants_differentiable p, fun s => ?_, fun s => ?_⟩
  · simp only [fePants]
    rw [show (1 : ℂ) - (1 - s) = s by ring]; ring
  · simp only [fePants, map_mul]
    rw [eulerInvFactor_conj,
        show (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) by rw [map_sub, map_one],
        eulerInvFactor_conj]

/-- **The completed local factor is zero-free across the open strip.**  The first factor is nonzero
because `Re s > 0`; the mirror factor is nonzero because `Re(1 − s) = 1 − Re s > 0`. -/
theorem fePants_ne_zero_on_strip (p : ℕ) (hp : 1 < p) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : fePants p s ≠ 0 := by
  refine mul_ne_zero (eulerInvFactor_ne_zero p hp h0) (eulerInvFactor_ne_zero p hp ?_)
  rw [Complex.sub_re, Complex.one_re]; linarith

/-! ### §3 The finite Euler bundle -/

/-- The finite Euler bundle `∏_{p∈P} fePants p s`: the FE-completed head of the Euler product over a
finite set of primes. -/
def feBundle (P : Finset ℕ) (s : ℂ) : ℂ := ∏ p ∈ P, fePants p s

/-- The bundle is FE + Schwarz: a finite product of FE + Schwarz members. -/
theorem feBundle_fESchwarz (P : Finset ℕ) : FESchwarz (feBundle P) := by
  unfold feBundle
  exact FESchwarz.finsetProd P fePants (fun p _ => fePants_fESchwarz p)

/-- **The bundle is zero-free across the open strip.**  A product of factors each nonzero there. -/
theorem feBundle_ne_zero_on_strip (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : feBundle P s ≠ 0 := by
  unfold feBundle
  rw [Finset.prod_ne_zero_iff]
  exact fun p hp => fePants_ne_zero_on_strip p (hP p hp) h0 h1

/-- The bundle has finite vanishing order at every point: it is entire and not identically zero
(nonvanishing at, e.g., `s = ½`), so by the identity theorem on the connected plane its order is
finite everywhere. -/
theorem feBundle_order_ne_top (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p) (ρ : ℂ) :
    analyticOrderAt (feBundle P) ρ ≠ ⊤ := by
  intro htop
  have hev0 : feBundle P =ᶠ[nhds ρ] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  have hw0 : (0 : ℝ) < (((1 / 2 : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; norm_num
  have hw1 : (((1 / 2 : ℝ) : ℂ)).re < 1 := by rw [Complex.ofReal_re]; norm_num
  have hzero : feBundle P (((1 / 2 : ℝ) : ℂ)) = 0 :=
    ((feBundle_fESchwarz P).1.differentiableOn.analyticOnNhd
      isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ ρ) hev0 (Set.mem_univ _)
  exact feBundle_ne_zero_on_strip P hP hw0 hw1 hzero

/-! ### §4 Divisor-inertness on the strip -/

/-- The decorated member `feBundle P · G` is FE + Schwarz whenever `G` is. -/
theorem feBundle_mul_fESchwarz (P : Finset ℕ) {G : ℂ → ℂ} (hG : FESchwarz G) :
    FESchwarz (fun s => feBundle P s * G s) :=
  (feBundle_fESchwarz P).mul hG

/-- **Divisor-inertness on the strip.**  Multiplying any differentiable `G` by the finite Euler
bundle changes no vanishing order at a strip point: `ord_ρ (feBundle P · G) = ord_ρ G` for
`0 < Re ρ < 1`, because the bundle is nonvanishing there (order `0`). -/
theorem feBundle_divisor_inert (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt (fun s => feBundle P s * G s) ρ = analyticOrderAt G ρ := by
  have hb_an : AnalyticAt ℂ (feBundle P) ρ := (feBundle_fESchwarz P).1.analyticAt ρ
  have hG_an : AnalyticAt ℂ G ρ := hG.analyticAt ρ
  have h := analyticOrderAt_mul hb_an hG_an
  rw [show (feBundle P * G) = (fun s => feBundle P s * G s) from rfl] at h
  rw [h, analyticOrderAt_eq_zero.mpr (Or.inr (feBundle_ne_zero_on_strip P hP h0 h1)), zero_add]

/-! ### §5 The finite-Euler-decorated class is soft -/

/-- The **finite-Euler-decorated class**: FE + Schwarz members carrying an exact finite Euler head. -/
def FiniteEulerClass (P : Finset ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ G, FESchwarz G ∧ ∀ s, f s = feBundle P s * G s

/-- **The decorated class carries charge at every off-line strip point.**  Decorating the bare
soft witness (the `V₄`-orbit quartic, a simple off-line zero) by the finite Euler bundle leaves its
order unchanged on the strip (`feBundle_divisor_inert`), so the decorated member still has an odd
zero — deck charge `−1 ≠ 1`.  The finite Euler head is invisible to the strip divisor. -/
theorem finiteEulerClass_carriesChargeAt (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    CarriesChargeAt (FiniteEulerClass P) ρ := by
  refine ⟨fun s => feBundle P s * orbitQuartic ρ s,
    ⟨orbitQuartic ρ, fESchwarz_orbitQuartic ρ, fun s => rfl⟩, ?_⟩
  rw [carrierCharge_one_eq_neg_one_pow,
      feBundle_divisor_inert P hP (orbitQuartic_differentiable ρ) h0 h1,
      orbitQuartic_order_one hre him]
  norm_num

/-- **The finite-Euler-decorated class is soft.**  At every off-line, off-real point `ρ` it plants a
member of nontrivial deck charge, exactly like the bare FE + Schwarz class.  The bundle has finite
order `m` at `ρ`; if `m` is even, decorate the orbit quartic (order `1`) to reach the odd order
`m + 1`; if `m` is odd, the bundle itself (decorate the constant `1`) already has the odd order `m`.
Either way a decorated member carries deck charge `−1 ≠ 1`.  On the strip this is the pure inertness
of §4; on the boundary lines it is the parity toggle of the bundle's own order. -/
theorem finiteEulerClass_isSoft (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p) :
    IsSoft (FiniteEulerClass P) := by
  intro ρ hre him
  have hmfin : analyticOrderAt (feBundle P) ρ ≠ ⊤ := feBundle_order_ne_top P hP ρ
  have hb_an : AnalyticAt ℂ (feBundle P) ρ := (feBundle_fESchwarz P).1.analyticAt ρ
  set m : ℕ := (analyticOrderAt (feBundle P) ρ).toNat with hm_def
  by_cases hpar : Even m
  · refine ⟨fun s => feBundle P s * orbitQuartic ρ s,
      ⟨orbitQuartic ρ, fESchwarz_orbitQuartic ρ, fun s => rfl⟩, ?_⟩
    have hq_an : AnalyticAt ℂ (orbitQuartic ρ) ρ := (orbitQuartic_differentiable ρ).analyticAt ρ
    have h := analyticOrderAt_mul hb_an hq_an
    rw [show (feBundle P * orbitQuartic ρ) = (fun s => feBundle P s * orbitQuartic ρ s) from rfl]
      at h
    rw [carrierCharge_one_eq_neg_one_pow, h, orbitQuartic_order_one hre him,
        ENat.toNat_add hmfin (by simp), ← hm_def, ENat.toNat_one,
        (hpar.add_one).neg_one_pow]
    norm_num
  · refine ⟨fun s => feBundle P s * (fun _ => (1 : ℂ)) s,
      ⟨fun _ => (1 : ℂ), fESchwarz_one, fun s => rfl⟩, ?_⟩
    have hc_an : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) ρ := analyticAt_const
    have hone : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) ρ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num))
    have h := analyticOrderAt_mul hb_an hc_an
    rw [show (feBundle P * (fun _ => (1 : ℂ))) = (fun s => feBundle P s * (fun _ => (1 : ℂ)) s)
      from rfl] at h
    rw [carrierCharge_one_eq_neg_one_pow, h, hone, add_zero, ← hm_def,
        (Nat.not_even_iff_odd.mp hpar).neg_one_pow]
    norm_num

/-- **The finite-Euler-decorated class cannot force RH-grade parity.**  Forcing parity by charge is
exactly the charge-free (categorical) cell (`forcesRHParity_iff_categorical`); the decorated class
is soft, hence carries off-line charge, hence is not categorical.  A finite exact Euler head adds no
parity-forcing power. -/
theorem finiteEulerClass_not_forcesRHParity (P : Finset ℕ) (hP : ∀ p ∈ P, 1 < p) :
    ¬ ForcesRHParity (FiniteEulerClass P) := by
  rw [forcesRHParity_iff_categorical]
  exact fun hcat => hcat (plantsArbitrary_imp_carriesCharge (finiteEulerClass_isSoft P hP))

end RHTower
