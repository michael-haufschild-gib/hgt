import GaloisForLFunctions.RHTower.BurnolCoPoissonIndicatorSource
import GaloisForLFunctions.RHTower.BurnolSoninBilateralKernel
import GaloisForLFunctions.RHTower.BurnolCoPoissonDilationChannels
import GaloisForLFunctions.RHTower.BurnolCoPoissonDouglasFactorization
import GaloisForLFunctions.RHTower.BurnolHedenmalmCompletionDomain
import GaloisForLFunctions.RHTower.XiHedenmalmSymmetricMultiplicity
import GaloisForLFunctions.RHTower.BurnolPrimeDilationCoPoissonQuotient
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinReflection
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful
import GaloisForLFunctions.RHTower.BurnolSoninCrossApertureRiesz

/-!
# Exact registration of the six paper-proven Burnol cards

Each declaration below is a type-identical alias of the concrete theorem serving one card.  The
aliases introduce no weakened hypotheses and no abstract replacement model; they make the exact
proof objects discoverable from a single module.  Open RH/sign/contraction consumers are not
asserted here.
-/

noncomputable section

namespace RHTower

/-! ## Bilateral aperture-defect energy law -/

/-- Exact signed forward/inverse defect-energy identity. -/
alias burnolBilateralApertureDefectEnergyCard :=
  burnol_bilateralApertureDefectEnergy

/-- Exact finite-holonomy quadratic form identity. -/
alias burnolBilateralApertureHolonomyCard :=
  burnol_bilateralApertureDefectEnergy_eq_holonomy

/-- Exact two-evaluator kernel of the bilateral aperture holonomy. -/
alias burnolBilateralApertureKernelCard :=
  burnolExtended_bilateralApertureHolonomy_kernel

/-! ## Co-Poisson Berezin diagonal reflection law -/

/-- Exact annihilator-fibre value, in hyperbolic form. -/
alias burnolCoPoissonBerezinReflectionCard :=
  burnolCoPoissonNormalizedHolonomy_eq_two_sinh_of_annihilator

/-- Faithfulness of the positive quotient-supported Berezin diagonal. -/
alias burnolCoPoissonBerezinFaithfulCard :=
  burnolCoPoissonBerezin_faithful_of_quotientSupported

/-! ## Co-Poisson quotient bilateral order law -/

/-- Exact forward-minus-inverse full-channel Gram decomposition. -/
alias burnolCoPoissonBilateralOrderGramCard :=
  burnolCoPoissonCompressedHolonomy_eq_fullChannel_gram_sub

/-- Exact infinite-dimensional Douglas equivalence between quotient order and contractive
factorization of the two actual dilation channels. -/
alias burnolCoPoissonBilateralOrderDouglasCard :=
  burnolCoPoissonCompressedHolonomy_neg_isPositive_iff_contractive_factorization

/-- Contractive factorization forces exact quotient flatness. -/
alias burnolCoPoissonBilateralOrderFlatnessCard :=
  burnolCoPoissonCompressedHolonomy_eq_zero_of_contractive_factorization

/-- The same factorization forces parity-channel cross-Gram decorrelation. -/
alias burnolCoPoissonBilateralOrderParityCard :=
  burnolCoPoissonForwardParityCrossGram_eq_zero_of_contractive_factorization

/-! ## Hedenmalm archimedean completion/domain/radical exchange -/

/-- Exact maximal-domain membership, nonzero source, and completed source-defect recurrence. -/
alias burnolHedenmalmArchimedeanCompletionCard :=
  burnolHedenmalm_archimedeanCompletion_domain_radicalExchange

/-- Symmetric source-quotient realization implies RH and simplicity. -/
alias burnolHedenmalmSymmetricRadicalCard :=
  symmetric_xiSourceQuotient_implies_rh_and_simple

/-! ## Prime-dilation co-Poisson quotient law -/

/-- Exact zero-radical prime-character resolvent identity. -/
alias burnolPrimeDilationCoPoissonQuotientCard :=
  burnolPrime_resolvent_quotient_identity

/-- Exact reflected prime-seam character split. -/
alias burnolPrimeDilationReflectionSeamCard :=
  orbitwiseScaleSeamCharge_eq_burnolPrimeCharacter_reflection

/-! ## Off-axis aperture-type rigidity -/

/-- Exact lower aperture-type estimate. -/
alias burnolSoninOffAxisApertureLowerCard :=
  norm_burnolExtendedSoninEvaluationVector_geometric_lower

/-- Exact upper aperture-type estimate. -/
alias burnolSoninOffAxisApertureUpperCard :=
  norm_burnolExtendedSoninEvaluationVector_geometric_upper

/-- Exact logarithmic aperture-type limit under its necessary nonzero-fibre premise. -/
alias burnolSoninOffAxisApertureLimitCard :=
  tendsto_log_norm_burnolExtendedSoninEvaluationVector

/-- Explicit unconditional inhabitation of every allowed Burnol co-Poisson source layer. -/
alias burnolCoPoissonSourceInhabitedCard :=
  nonempty_burnolCoPoissonSource

end RHTower
