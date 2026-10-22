import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZParityLocalTemperedFEReflectionNoGo

/-!
# Positive nonlocal FZZ reflection collapses to reciprocal delay

The literal FZZ parity-delay density is the positive Fermi kernel

`F(t) = 1 / (exp t + 1)`.

The local reflection audit proved that pointwise Mellin reflection forces reciprocal delay and an
exponentially singular weight.  This module closes the positive nonlocal loophole.  Let `K_t` be
any finite positive kernel on positive delays and require only the first three reflected density
rows

```text
∫ F(u) dK_t(u)    = t⁻¹ F(t),
∫ u F(u) dK_t(u)  = t⁻² F(t),
∫ u² F(u) dK_t(u) = t⁻³ F(t).
```

Writing `a = t⁻¹`, these identities give the exact zero-variance law

`∫ (u-a)² F(u) dK_t(u) = 0`.

Positivity of both the kernel and `F` forces `K_t` to be concentrated at `a`.  The zeroth row then
fixes its total mass as

`t⁻¹ (exp(t⁻¹)+1)/(exp(t)+1)`,

exactly the unique local reflection weight.  Therefore positive nonlocal spread cannot soften the
ultraviolet singularity: every polynomially tempered positive finite-kernel implementation is
impossible.  Any surviving FZZ-P completion must be signed/distributional or retain the forced
essential singularity.

The zero-variance argument is classical.  Candidate novelty is the source-specific three-row
classification and its consequence for the FZZ-P RH route.

`[FZZ-P ROUTE KILL] [POSITIVE NONLOCAL COLLAPSE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
-/

open Filter Topology Asymptotics MeasureTheory Set

namespace RHTower

noncomputable section

/-- Positive physical delay. -/
abbrev FZZCigarPositiveDelay := {t : ℝ // 0 < t}

/-- Reciprocal delay preserves the positive ray. -/
def fzzCigarPositiveDelayReciprocal (t : FZZCigarPositiveDelay) :
    FZZCigarPositiveDelay :=
  ⟨(t : ℝ)⁻¹, inv_pos.mpr t.property⟩

/-- Literal parity-delay density restricted to positive delays. -/
def fzzCigarPositiveDelayDensity (t : FZZCigarPositiveDelay) : ℝ :=
  fzzCigarParityDelay (t : ℝ)

/-- A positive finite nonlocal kernel implementing the first three reflected Mellin-density rows
of the literal FZZ parity source.  Integrability is included as finite-action data, not obtained by
target fitting. -/
structure FZZCigarParityPositiveNonlocalFEReflectionData where
  kernel : FZZCigarPositiveDelay → Measure FZZCigarPositiveDelay
  kernel_finite : ∀ t, IsFiniteMeasure (kernel t)
  grade_zero_integrable : ∀ t, Integrable
    (fun u : FZZCigarPositiveDelay => fzzCigarPositiveDelayDensity u) (kernel t)
  grade_one_integrable : ∀ t, Integrable
    (fun u : FZZCigarPositiveDelay =>
      (u : ℝ) * fzzCigarPositiveDelayDensity u) (kernel t)
  grade_two_integrable : ∀ t, Integrable
    (fun u : FZZCigarPositiveDelay =>
      (u : ℝ) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u) (kernel t)
  grade_zero : ∀ t,
    ∫ u : FZZCigarPositiveDelay, fzzCigarPositiveDelayDensity u ∂kernel t =
      (t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t
  grade_one : ∀ t,
    ∫ u : FZZCigarPositiveDelay,
      (u : ℝ) * fzzCigarPositiveDelayDensity u ∂kernel t =
      (t : ℝ)⁻¹ ^ (2 : ℕ) * fzzCigarPositiveDelayDensity t
  grade_two : ∀ t,
    ∫ u : FZZCigarPositiveDelay,
      (u : ℝ) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u ∂kernel t =
      (t : ℝ)⁻¹ ^ (3 : ℕ) * fzzCigarPositiveDelayDensity t

private theorem fzzCigarPositiveDelayDensity_pos (t : FZZCigarPositiveDelay) :
    0 < fzzCigarPositiveDelayDensity t := by
  rw [fzzCigarPositiveDelayDensity, fzzCigarParityDelay_eq_fermi t.property]
  positivity

/-- **Positive nonlocal collapse.**  Three adjacent reflected Mellin-density rows have zero
Fermi-weighted conditional variance.  Every positive finite kernel is therefore concentrated at
reciprocal delay. -/
theorem FZZCigarParityPositiveNonlocalFEReflectionData.kernel_ae_reciprocal
    (D : FZZCigarParityPositiveNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    ∀ᵐ u ∂D.kernel t, u = fzzCigarPositiveDelayReciprocal t := by
  let a : ℝ := (t : ℝ)⁻¹
  have hlinear : Integrable
      (fun u : FZZCigarPositiveDelay =>
        ((u : ℝ) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u -
          (2 * a) * ((u : ℝ) * fzzCigarPositiveDelayDensity u)) +
          a ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u)
      (D.kernel t) :=
    ((D.grade_two_integrable t).sub
      ((D.grade_one_integrable t).const_mul (2 * a))).add
        ((D.grade_zero_integrable t).const_mul (a ^ (2 : ℕ)))
  have hvarInt : Integrable
      (fun u : FZZCigarPositiveDelay =>
        ((u : ℝ) - a) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u)
      (D.kernel t) := by
    refine hlinear.congr ?_
    filter_upwards with u
    ring
  have hnonneg : 0 ≤ᵐ[D.kernel t]
      (fun u : FZZCigarPositiveDelay =>
        ((u : ℝ) - a) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u) :=
    Eventually.of_forall fun u =>
      mul_nonneg (sq_nonneg _) (fzzCigarPositiveDelayDensity_pos u).le
  have hvarZero :
      (∫ u : FZZCigarPositiveDelay,
        ((u : ℝ) - a) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u ∂D.kernel t) = 0 := by
    calc
      _ = ∫ u : FZZCigarPositiveDelay,
          (((u : ℝ) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u -
            (2 * a) * ((u : ℝ) * fzzCigarPositiveDelayDensity u)) +
            a ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u) ∂D.kernel t := by
        apply integral_congr_ae
        filter_upwards with u
        ring
      _ =
          (∫ u : FZZCigarPositiveDelay,
              (u : ℝ) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u ∂D.kernel t) -
            (2 * a) *
              (∫ u : FZZCigarPositiveDelay,
                (u : ℝ) * fzzCigarPositiveDelayDensity u ∂D.kernel t) +
            a ^ (2 : ℕ) *
              (∫ u : FZZCigarPositiveDelay,
                fzzCigarPositiveDelayDensity u ∂D.kernel t) := by
        have hshape :
            (fun u : FZZCigarPositiveDelay =>
              ((u : ℝ) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u -
                (2 * a) * ((u : ℝ) * fzzCigarPositiveDelayDensity u)) +
                a ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u) =
              ((fun u : FZZCigarPositiveDelay =>
                  (u : ℝ) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u) -
                (fun u : FZZCigarPositiveDelay =>
                  (2 * a) * ((u : ℝ) * fzzCigarPositiveDelayDensity u))) +
                (fun u : FZZCigarPositiveDelay =>
                  a ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u) := by
          rfl
        rw [hshape]
        calc
          _ =
              (∫ u : FZZCigarPositiveDelay,
                ((fun v : FZZCigarPositiveDelay =>
                    (v : ℝ) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity v) -
                  (fun v : FZZCigarPositiveDelay =>
                    (2 * a) * ((v : ℝ) * fzzCigarPositiveDelayDensity v))) u
                  ∂D.kernel t) +
                (∫ u : FZZCigarPositiveDelay,
                  a ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u ∂D.kernel t) :=
            integral_add
              ((D.grade_two_integrable t).sub
                ((D.grade_one_integrable t).const_mul (2 * a)))
              ((D.grade_zero_integrable t).const_mul (a ^ (2 : ℕ)))
          _ =
              ((∫ u : FZZCigarPositiveDelay,
                  (u : ℝ) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u ∂D.kernel t) -
                (∫ u : FZZCigarPositiveDelay,
                  (2 * a) * ((u : ℝ) * fzzCigarPositiveDelayDensity u)
                    ∂D.kernel t)) +
                (∫ u : FZZCigarPositiveDelay,
                  a ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u ∂D.kernel t) := by
            have hsub := integral_sub (D.grade_two_integrable t)
              ((D.grade_one_integrable t).const_mul (2 * a))
            exact congrArg
              (fun x : ℝ => x +
                ∫ u : FZZCigarPositiveDelay,
                  a ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u ∂D.kernel t)
              hsub
          _ = _ := by rw [integral_const_mul, integral_const_mul]
      _ = 0 := by
        rw [D.grade_zero t, D.grade_one t, D.grade_two t]
        dsimp only [a]
        ring
  have haeZero :
      (fun u : FZZCigarPositiveDelay =>
        ((u : ℝ) - a) ^ (2 : ℕ) * fzzCigarPositiveDelayDensity u) =ᵐ[D.kernel t] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hvarInt).mp hvarZero
  filter_upwards [haeZero] with u hu
  have hdensity := fzzCigarPositiveDelayDensity_pos u
  have hsquare : ((u : ℝ) - a) ^ (2 : ℕ) = 0 := by
    rcases mul_eq_zero.mp hu with h | h
    · exact h
    · exact False.elim (hdensity.ne' h)
  apply Subtype.ext
  change (u : ℝ) = a
  nlinarith [sq_nonneg ((u : ℝ) - a)]

/-- Total positive kernel mass at one input delay. -/
def FZZCigarParityPositiveNonlocalFEReflectionData.kernelMass
    (D : FZZCigarParityPositiveNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) : ℝ :=
  (D.kernel t).real Set.univ

/-- Exact measure classification: a positive nonlocal reflection kernel is a single reciprocal-
delay atom. -/
theorem FZZCigarParityPositiveNonlocalFEReflectionData.kernel_eq_atom
    (D : FZZCigarParityPositiveNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    D.kernel t =
      D.kernel t {fzzCigarPositiveDelayReciprocal t} •
        Measure.dirac (fzzCigarPositiveDelayReciprocal t) := by
  have hae : ∀ᵐ u ∂D.kernel t,
      u ∈ ({fzzCigarPositiveDelayReciprocal t} : Set FZZCigarPositiveDelay) := by
    simpa only [Set.mem_singleton_iff] using D.kernel_ae_reciprocal t
  calc
    D.kernel t = (D.kernel t).restrict
        {fzzCigarPositiveDelayReciprocal t} :=
      (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ = D.kernel t {fzzCigarPositiveDelayReciprocal t} •
        Measure.dirac (fzzCigarPositiveDelayReciprocal t) :=
      Measure.restrict_singleton _ _

theorem FZZCigarParityPositiveNonlocalFEReflectionData.kernelMass_mul_density
    (D : FZZCigarParityPositiveNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    D.kernelMass t *
        fzzCigarPositiveDelayDensity (fzzCigarPositiveDelayReciprocal t) =
      (t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t := by
  letI : IsFiniteMeasure (D.kernel t) := D.kernel_finite t
  have hae :
      (fun u : FZZCigarPositiveDelay => fzzCigarPositiveDelayDensity u) =ᵐ[D.kernel t]
        fun _ => fzzCigarPositiveDelayDensity
          (fzzCigarPositiveDelayReciprocal t) := by
    filter_upwards [D.kernel_ae_reciprocal t] with u hu
    rw [hu]
  calc
    D.kernelMass t *
          fzzCigarPositiveDelayDensity (fzzCigarPositiveDelayReciprocal t) =
        ∫ _ : FZZCigarPositiveDelay,
          fzzCigarPositiveDelayDensity (fzzCigarPositiveDelayReciprocal t)
            ∂D.kernel t := by
      rw [integral_const]
      simp [FZZCigarParityPositiveNonlocalFEReflectionData.kernelMass,
        smul_eq_mul]
    _ = ∫ u : FZZCigarPositiveDelay,
          fzzCigarPositiveDelayDensity u ∂D.kernel t :=
      integral_congr_ae hae.symm
    _ = (t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t := D.grade_zero t

/-- The atom mass is the unique source-faithful local FZZ reflection weight. -/
theorem FZZCigarParityPositiveNonlocalFEReflectionData.kernelMass_eq
    (D : FZZCigarParityPositiveNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    D.kernelMass t =
      (t : ℝ)⁻¹ * (Real.exp (t : ℝ)⁻¹ + 1) /
        (Real.exp (t : ℝ) + 1) := by
  have hmass := D.kernelMass_mul_density t
  change D.kernelMass t * fzzCigarParityDelay (t : ℝ)⁻¹ =
      (t : ℝ)⁻¹ * fzzCigarParityDelay (t : ℝ) at hmass
  rw [fzzCigarParityDelay_eq_fermi (inv_pos.mpr t.property),
      fzzCigarParityDelay_eq_fermi t.property] at hmass
  have hden : Real.exp (t : ℝ) + 1 ≠ 0 := by positivity
  have hinvden : Real.exp (t : ℝ)⁻¹ + 1 ≠ 0 := by positivity
  field_simp [hden, hinvden] at hmass ⊢
  nlinarith

/-- Singular local survivor exposed by the positive-kernel classification. -/
def fzzCigarParityForcedLocalFEReflectionData :
    FZZCigarParityLocalFEReflectionData where
  energyMap t := t⁻¹
  weight t := t⁻¹ * (Real.exp t⁻¹ + 1) / (Real.exp t + 1)
  grade_one := by
    intro t ht
    rw [fzzCigarParityDelay_eq_fermi (inv_pos.mpr ht),
      fzzCigarParityDelay_eq_fermi ht]
    have hden : Real.exp t + 1 ≠ 0 := by positivity
    have hinvden : Real.exp t⁻¹ + 1 ≠ 0 := by positivity
    field_simp [hden, hinvden]
  grade_two := by
    intro t ht
    rw [fzzCigarParityDelay_eq_fermi (inv_pos.mpr ht),
      fzzCigarParityDelay_eq_fermi ht]
    have hden : Real.exp t + 1 ≠ 0 := by positivity
    have hinvden : Real.exp t⁻¹ + 1 ≠ 0 := by positivity
    field_simp [hden, hinvden]

def fzzCigarParityPositiveNonlocalUVDelay (n : ℕ) : FZZCigarPositiveDelay :=
  ⟨(((n + 1 : ℕ) : ℝ))⁻¹, inv_pos.mpr (by positivity)⟩

/-- Nonlocal-kernel mass on the ultraviolet reciprocal-depth ray. -/
def FZZCigarParityPositiveNonlocalFEReflectionData.uvKernelMass
    (D : FZZCigarParityPositiveNonlocalFEReflectionData) (n : ℕ) : ℝ :=
  D.kernelMass (fzzCigarParityPositiveNonlocalUVDelay n)

theorem FZZCigarParityPositiveNonlocalFEReflectionData.uvKernelMass_eq
    (D : FZZCigarParityPositiveNonlocalFEReflectionData) (n : ℕ) :
    D.uvKernelMass n =
      ((n + 1 : ℕ) : ℝ) *
        (Real.exp ((n + 1 : ℕ) : ℝ) + 1) /
          (Real.exp (((n + 1 : ℕ) : ℝ))⁻¹ + 1) := by
  rw [FZZCigarParityPositiveNonlocalFEReflectionData.uvKernelMass,
    D.kernelMass_eq]
  simp only [fzzCigarParityPositiveNonlocalUVDelay, Subtype.coe_mk]
  rw [inv_inv]

theorem FZZCigarParityPositiveNonlocalFEReflectionData.uvKernelMass_eq_forcedLocal
    (D : FZZCigarParityPositiveNonlocalFEReflectionData) :
    D.uvKernelMass = fzzCigarParityForcedLocalFEReflectionData.uvWeight := by
  funext n
  rw [D.uvKernelMass_eq,
    fzzCigarParityForcedLocalFEReflectionData.uvWeight_eq]

/-- Polynomial tempering of a positive nonlocal kernel means polynomial total mass on the
ultraviolet reciprocal-depth ray. -/
def FZZCigarParityPositiveNonlocalFEReflectionData.PolynomiallyTempered
    (D : FZZCigarParityPositiveNonlocalFEReflectionData) : Prop :=
  ∃ K : ℕ, D.uvKernelMass =O[atTop]
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ K)

/-- Positive nonlocal spread cannot evade the local ultraviolet singularity. -/
theorem FZZCigarParityPositiveNonlocalFEReflectionData.not_polynomiallyTempered
    (D : FZZCigarParityPositiveNonlocalFEReflectionData) :
    ¬ D.PolynomiallyTempered := by
  rintro ⟨K, hK⟩
  have hforced : fzzCigarParityForcedLocalFEReflectionData.PolynomiallyTempered := by
    refine ⟨K, ?_⟩
    simpa only [D.uvKernelMass_eq_forcedLocal] using hK
  exact fzzCigarParityForcedLocalFEReflectionData.not_polynomiallyTempered hforced

/-- **[FZZ-P POSITIVE NONLOCAL ROUTE KILL].**  No polynomially tempered positive finite
nonlocal kernel can implement the first three reflected Mellin-density rows of the literal FZZ
parity-delay source. -/
theorem no_polynomiallyTempered_FZZCigarParityPositiveNonlocalFEReflectionData :
    ¬ ∃ D : FZZCigarParityPositiveNonlocalFEReflectionData,
      D.PolynomiallyTempered := by
  rintro ⟨D, hD⟩
  exact D.not_polynomiallyTempered hD

end

end RHTower
