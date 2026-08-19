import GaloisForLFunctions.HTGeometry.QuasiAbelianCosetPoincareJet
import GaloisForLFunctions.HTGeometry.QuasiAbelianDampedFactorExtension
import GaloisForLFunctions.HTGeometry.AbePositiveTorusFreeWitnesses

/-!
# Constructing a damped packet lift from a damping family

`AbeDampedJetPacketLift` was an interface: its `jet_decomposition` and `remainderMajorant` were
asserted, not derived.  This file derives both from *primitive, checkable* data — a complement
embedding for `ΓH ≤ Γ`, and a family of lower-automorphic seeds that

* agree with the given lower column on the finite jet packet, and
* whose complement Poincaré terms carry the polynomial-Gaussian damping bound.

Everything else — that the partial Poincaré sum is an upper automorphic form, that its jets split
as seed plus complement remainder — is now a theorem.  This is the same move that turned the
`gaussianMajorant` field of `AbePositiveFactorPresentation` into a consequence of
`HasLatticeExponentialGrowth` at the base of the tower.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Primitive data for one damped packet lift: a complement of `ΓH` in `Γ`, and a `B`-family of
lower seeds with the packet jets of the given lower column and an exponentially damped complement
Poincaré remainder. -/
structure AbeDampingPacketData {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    (lower : AutomorphicFactor d ΓH) (upper : AutomorphicFactor d Γ)
    {I : Type u} [Fintype I] [DecidableEq I] (w : I → Fin d → ℂ) (m : I → ℕ)
    (lowerColumn : FiniteJetPacketIndex d I m → lower.forms) where
  le : ΓH ≤ Γ
  compat : ∀ (η : Fin d → ℂ) (hη : η ∈ ΓH),
    (upper.factor ⟨η, le hη⟩).1 = (lower.factor ⟨η, hη⟩).1
  comp : (Fin c → ℤ) →+ (Fin d → ℂ)
  comp_mem : ∀ z, comp z ∈ Γ
  decomp : ∀ δ ∈ Γ, ∃ η ∈ ΓH, ∃ z : Fin c → ℤ, δ = η + comp z
  seed : ℝ → FiniteJetPacketIndex d I m → MultivariateEntire d
  seed_mem : ∀ B j, seed B j ∈ lower.forms
  seed_jet : ∀ (B : ℝ) (i j : FiniteJetPacketIndex d I m),
    multiIndexJetEvalCLM (w i.1) i.2.1 (seed B j)
      = multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1
  normal : ∀ (B : ℝ) (j : FiniteJetPacketIndex d I m), SummableLocallyUniformlyOn
    (fun z : Fin c → ℤ =>
      poincareTerm upper (seed B j) (complementEmbedding comp comp_mem z)) Set.univ
  majorant : ∃ (A : Fin c → ℕ) (sigma : Fin c → ℝ) (r : ℕ) (delta C : ℝ),
      (∀ i, 0 < sigma i) ∧ 0 < delta ∧ 0 ≤ C ∧
      ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
        ‖multiIndexJetEvalCLM (w i.1) i.2.1
            (poincareTermEntire upper (seed B j) (complementEmbedding comp comp_mem z))‖
          ≤ (C * (B ^ r * Real.exp (-(delta * B)))) *
              polynomialGaussianLatticeWeight (Fin c) A sigma z

theorem polynomialGaussianLatticeWeight_nonneg (ι : Type) [Fintype ι] (A : ι → ℕ)
    (sigma : ι → ℝ) (z : ι → ℤ) : 0 ≤ polynomialGaussianLatticeWeight ι A sigma z := by
  rw [polynomialGaussianLatticeWeight]
  exact Finset.prod_nonneg fun i _ => by positivity

/-- **The damped packet lift is constructible.** -/
def AbeDampingPacketData.toLift {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    {I : Type u} [Fintype I] [DecidableEq I] {w : I → Fin d → ℂ} {m : I → ℕ}
    {lowerColumn : FiniteJetPacketIndex d I m → lower.forms}
    (D : AbeDampingPacketData (c := c) lower upper w m lowerColumn) :
    AbeDampedJetPacketLift upper w m (fun j => (lowerColumn j).1) where
  complementRank := c
  upperColumn := fun B j =>
    ⟨cosetPoincareSeriesEntire upper D.comp D.comp_mem (D.seed B j) (D.normal B j),
      cosetPoincareSeriesEntire_mem_forms lower upper D.le D.compat D.comp D.comp_mem
        (fun δ hδ => D.decomp δ hδ) (D.seed B j) (D.seed_mem B j) (D.normal B j)⟩
  remainderTerm := fun B z i j =>
    if z = 0 then 0
    else multiIndexJetEvalCLM (w i.1) i.2.1
      (poincareTermEntire upper (D.seed B j) (complementEmbedding D.comp D.comp_mem z))
  jet_decomposition := by
    intro B i j
    have h := jet_cosetPoincareSeriesEntire_eq_seed_add_tail upper D.comp D.comp_mem
      (D.seed B j) (D.normal B j) (w i.1) i.2.1
    rw [show ((⟨cosetPoincareSeriesEntire upper D.comp D.comp_mem (D.seed B j) (D.normal B j),
      cosetPoincareSeriesEntire_mem_forms lower upper D.le D.compat D.comp D.comp_mem
        (fun δ hδ => D.decomp δ hδ) (D.seed B j) (D.seed_mem B j) (D.normal B j)⟩ :
        upper.forms) : MultivariateEntire d)
      = cosetPoincareSeriesEntire upper D.comp D.comp_mem (D.seed B j) (D.normal B j) from rfl]
    rw [h, D.seed_jet B i j]
  remainderMajorant := by
    obtain ⟨A, sigma, r, delta, C, hsigma, hdelta, hC, hbound⟩ := D.majorant
    refine ⟨A, sigma, r, delta, C, hsigma, hdelta, hC, ?_⟩
    intro B hB z i j
    by_cases hz : z = 0
    · rw [if_pos hz, norm_zero]
      have h1 : (0:ℝ) ≤ C * (B ^ r * Real.exp (-(delta * B))) := by positivity
      exact mul_nonneg h1 (polynomialGaussianLatticeWeight_nonneg (Fin c) A sigma z)
    · rw [if_neg hz]
      exact hbound B hB z i j hz


/-- Abe's damping estimate, as a property of the pair of factors: every finite jet packet and every
lower column admits a damping family. -/
def HasAbeDampingFamily {d : ℕ} (c : ℕ) {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    (lower : AutomorphicFactor d ΓH) (upper : AutomorphicFactor d Γ) : Prop :=
  ∀ (I : Type u) [Fintype I] [DecidableEq I] (w : I → Fin d → ℂ) (m : I → ℕ)
    (lowerColumn : FiniteJetPacketIndex d I m → lower.forms),
    Nonempty (AbeDampingPacketData (c := c) lower upper w m lowerColumn)

/-- **The subgroup-rank extension step is constructible from the damping estimate alone.** -/
def abeDampedFactorExtensionOfDampingFamily {d : ℕ} {c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    (hle : ΓH ≤ Γ) (h : HasAbeDampingFamily.{u} c lower upper) :
    AbeDampedFactorExtension.{u} lower upper where
  subgroup_le := hle
  liftPacket := fun I _ _ w m lowerColumn => (h I w m lowerColumn).some.toLift

/-- **All-order jet ampleness is transported by the damping estimate.** -/
theorem jetAmpleEveryFiniteOrder_of_hasAbeDampingFamily {d : ℕ} {c : ℕ}
    {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    (hle : ΓH ≤ Γ) (h : HasAbeDampingFamily.{u} c lower upper)
    (hlower : AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} lower) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} upper :=
  (abeDampedFactorExtensionOfDampingFamily hle h).jetAmpleEveryFiniteOrder hlower

/-- **Abe positivity is transported by the damping estimate.** -/
theorem isAbePositiveTorusless_of_hasAbeDampingFamily {d : ℕ} {c : ℕ}
    {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    (hle : ΓH ≤ Γ) (h : HasAbeDampingFamily.{u} c lower upper)
    (hlower : AutomorphicFactor.IsAbePositiveTorusless.{u} lower) :
    AutomorphicFactor.IsAbePositiveTorusless.{u} upper :=
  isAbePositiveTorusless_extension hlower (abeDampedFactorExtensionOfDampingFamily hle h)

end

end GaloisForLFunctions.HTGeometry
