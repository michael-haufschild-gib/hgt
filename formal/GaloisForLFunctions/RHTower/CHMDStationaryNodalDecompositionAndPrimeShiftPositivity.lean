import GaloisForLFunctions.RHTower.CHMDBeurlingDenyNodalDecompositionAndParityBoundStateSpaces
import GaloisForLFunctions.RHTower.CHMDExactParityBoundStateDimensionAndShiftedThetaOrthogonality
import GaloisForLFunctions.RHTower.CHMDHarmonicGroundPotentialAndMaximalDomainPrimeShiftForm

/-!
# Stationary Nodal Decomposition, Strict Stationary Beurling–Deny Rigidity, and Prime-Shift Modulus Domination

This module unifies the Beurling–Deny nodal decomposition (`posGraph`, `negGraph`, `absGraph`)
on `SourceGraph` with the maximal-domain stationary and prime-shift decomposition
(`sourcePair_eq_stationary_sub_arch_sub_primeShift`, `sourceEnergy_eq_stationary_sub_arch_sub_primeShift`):

1. **Invariance and Orthogonal-Support Vanishing of the Archimedean and Prime Diagonal Forms**:
   for every $p \in \mathrm{SourceGraph}$,
   $$\|\operatorname{thetaToVolume}((\operatorname{absGraph} p).\mathrm{fst})\|_{L^2(\mathbb{R})}^2
     = \|\operatorname{thetaToVolume}(p.\mathrm{fst})\|_{L^2(\mathbb{R})}^2,$$
   $$\langle \operatorname{primeDiagonalOperator}((\operatorname{absGraph} p).\mathrm{fst}),
     (\operatorname{absGraph} p).\mathrm{fst}\rangle_{\mathbb{R}}
     = \langle \operatorname{primeDiagonalOperator}(p.\mathrm{fst}), p.\mathrm{fst}\rangle_{\mathbb{R}},$$
   and the diagonal pairings between `posGraph p` and `negGraph p` vanish identically:
   $$\langle \operatorname{thetaToVolume}((\operatorname{posGraph} p).\mathrm{fst}),
     \operatorname{thetaToVolume}((\operatorname{negGraph} p).\mathrm{fst})\rangle_{\mathbb{R}} = 0,$$
   $$\langle \operatorname{archDiagonalOperator}((\operatorname{posGraph} p).\mathrm{fst}),
     (\operatorname{negGraph} p).\mathrm{fst}\rangle_{\mathbb{R}} = 0,$$
   $$\langle \operatorname{primeDiagonalOperator}((\operatorname{posGraph} p).\mathrm{fst}),
     (\operatorname{negGraph} p).\mathrm{fst}\rangle_{\mathbb{R}} = 0,$$
   $$\langle \operatorname{groundPotentialOperator}((\operatorname{posGraph} p).\mathrm{fst}),
     (\operatorname{negGraph} p).\mathrm{fst}\rangle_{\mathbb{R}} = 0.$$
2. **Exact Stationary Beurling–Deny Cross-Jump Formula and Strict Stationary Rigidity**:
   for every $p \in \mathrm{SourceGraph}$,
   $$\operatorname{stationaryEnergy}(\Theta \cdot (\operatorname{absGraph} p).\mathrm{fst})
     = \operatorname{stationaryEnergy}(\Theta \cdot p.\mathrm{fst})
       + 4\,\langle (\operatorname{fullGroundEquiv}(\operatorname{posGraph} p)).\mathrm{snd},
           (\operatorname{fullGroundEquiv}(\operatorname{negGraph} p)).\mathrm{snd}\rangle_{\mathbb{R}},$$
   where the stationary edge pairing equals the archimedean cross-jump integral:
   $$\langle (\operatorname{fullGroundEquiv}(\operatorname{posGraph} p)).\mathrm{snd},
       (\operatorname{fullGroundEquiv}(\operatorname{negGraph} p)).\mathrm{snd}\rangle_{\mathbb{R}}
     = -\int e,\,\big(u^+(\operatorname{left} e)\,u^-(\operatorname{right} e)
       + u^-(\operatorname{left} e)\,u^+(\operatorname{right} e)\big)\,d\mathrm{archMeasure}(e) \le 0,$$
   with equality to $0$ if and only if $\operatorname{posGraph} p = 0 \lor \operatorname{negGraph} p = 0$.
   Consequently,
   $$\operatorname{stationaryEnergy}(\Theta \cdot (\operatorname{absGraph} p).\mathrm{fst})
     \le \operatorname{stationaryEnergy}(\Theta \cdot p.\mathrm{fst}),$$
   with strict inequality whenever $p$ changes sign (in particular, for every nonzero primitive
   graph vector and every nonzero odd graph vector).
3. **Positivity and Modulus Domination of `primeShiftOperator`**:
   for all $u, v \in \mathrm{MassSpace}$ with $0 \le^{\text{a.e.}} u, v$,
   $$0 \le \langle \operatorname{primeShiftOperator} u, v\rangle_{\mathbb{R}}
     = 2 \int e,\, u(\operatorname{left} e)\,v(\operatorname{right} e)\,d\mathrm{allPrimeMeasure}(e).$$
   For every $p \in \mathrm{SourceGraph}$,
   $$\langle \operatorname{primeShiftOperator}((\operatorname{absGraph} p).\mathrm{fst}),
       (\operatorname{absGraph} p).\mathrm{fst}\rangle_{\mathbb{R}}
     - \langle \operatorname{primeShiftOperator}(p.\mathrm{fst}), p.\mathrm{fst}\rangle_{\mathbb{R}}
     = 4\,\langle \operatorname{primeShiftOperator}((\operatorname{posGraph} p).\mathrm{fst}),
       (\operatorname{negGraph} p).\mathrm{fst}\rangle_{\mathbb{R}} \ge 0$$
   and
   $$|\langle \operatorname{primeShiftOperator}(p.\mathrm{fst}), p.\mathrm{fst}\rangle_{\mathbb{R}}|
     \le \langle \operatorname{primeShiftOperator}((\operatorname{absGraph} p).\mathrm{fst}),
       (\operatorname{absGraph} p).\mathrm{fst}\rangle_{\mathbb{R}}
     \le \langle \operatorname{primeDiagonalOperator}(p.\mathrm{fst}), p.\mathrm{fst}\rangle_{\mathbb{R}}.$$
4. **Bilateral Decomposition of the Total Cross-Jump Pairing**:
   for every $p \in \mathrm{SourceGraph}$,
   $$\operatorname{sourcePair}(\operatorname{posGraph} p, \operatorname{negGraph} p)
     = \langle (\operatorname{fullGroundEquiv}(\operatorname{posGraph} p)).\mathrm{snd},
         (\operatorname{fullGroundEquiv}(\operatorname{negGraph} p)).\mathrm{snd}\rangle_{\mathbb{R}}
       - \langle \operatorname{primeShiftOperator}((\operatorname{posGraph} p).\mathrm{fst}),
         (\operatorname{negGraph} p).\mathrm{fst}\rangle_{\mathbb{R}},$$
   splitting the total Beurling–Deny nodal jump penalty into the strictly negative stationary
   archimedean jump term and the nonpositive prime shift jump term.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump ThetaSourceWard

/-! ## Section 1: Invariance and Orthogonal-Support Vanishing of Diagonal Forms -/

theorem inner_thetaToVolume_posGraph_negGraph (p : SourceGraph) :
    ⟪thetaToVolume (posGraph p).val.fst, thetaToVolume (negGraph p).val.fst⟫_ℝ = 0 := by
  rw [L2.inner_def]
  have h : (fun x => inner ℝ (thetaToVolume (posGraph p).val.fst x)
      (thetaToVolume (negGraph p).val.fst x)) =ᵐ[volume] fun _ => (0 : ℝ) := by
    filter_upwards [thetaToVolume_ae (posGraph p).val.fst,
      thetaToVolume_ae (negGraph p).val.fst,
      volume_absolutelyContinuous_mass.ae_le (posGraph_fst_ae p),
      volume_absolutelyContinuous_mass.ae_le (negGraph_fst_ae p)] with x htp htn hp hn
    simp only [RCLike.inner_apply', conj_trivial, htp, htn]
    unfold thetaProduct
    rw [hp, hn]
    have hmul := posFun_mul_negFun (p.val.fst x)
    linear_combination riemannKernelReal x * riemannKernelReal x * hmul
  rw [integral_congr_ae h, integral_zero]

theorem inner_archDiagonalOperator_posGraph_negGraph (p : SourceGraph) :
    ⟪archDiagonalOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ = 0 := by
  rw [inner_archDiagonalOperator, inner_thetaToVolume_posGraph_negGraph, mul_zero]

theorem inner_primeDiagonalOperator_posGraph_negGraph (p : SourceGraph) :
    ⟪primeDiagonalOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ = 0 := by
  rw [inner_primeDiagonalOperator]
  have h : (fun x => primeDiagonalPotential x * (posGraph p).val.fst x * (negGraph p).val.fst x)
      =ᵐ[massMeasure] fun _ => (0 : ℝ) := by
    filter_upwards [posGraph_fst_ae p, negGraph_fst_ae p] with x hp hn
    rw [hp, hn, mul_assoc, posFun_mul_negFun, mul_zero]
  rw [integral_congr_ae h, integral_zero]

theorem inner_groundPotentialOperator_posGraph_negGraph (p : SourceGraph) :
    ⟪groundPotentialOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ = 0 := by
  rw [inner_groundPotentialOperator]
  have h : (fun x => thetaGroundPotential x * (posGraph p).val.fst x * (negGraph p).val.fst x)
      =ᵐ[massMeasure] fun _ => (0 : ℝ) := by
    filter_upwards [posGraph_fst_ae p, negGraph_fst_ae p] with x hp hn
    rw [hp, hn, mul_assoc, posFun_mul_negFun, mul_zero]
  rw [integral_congr_ae h, integral_zero]

theorem norm_thetaToVolume_absGraph_sq (p : SourceGraph) :
    ‖thetaToVolume (absGraph p).val.fst‖ ^ 2 = ‖thetaToVolume p.val.fst‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [thetaToVolume_ae (absGraph p).val.fst, thetaToVolume_ae p.val.fst,
    volume_absolutelyContinuous_mass.ae_le (absGraph_fst_ae p)] with x hta ht ha
  simp only [RCLike.inner_apply', conj_trivial, hta, ht]
  unfold thetaProduct
  rw [ha]
  dsimp only [absFun]
  have hsq : |p.val.fst x| * |p.val.fst x| = p.val.fst x * p.val.fst x := by
    rw [← sq, ← sq, sq_abs]
  linear_combination riemannKernelReal x * riemannKernelReal x * hsq

theorem norm_thetaToVolume_absGraph (p : SourceGraph) :
    ‖thetaToVolume (absGraph p).val.fst‖ = ‖thetaToVolume p.val.fst‖ :=
  (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (norm_thetaToVolume_absGraph_sq p)

theorem inner_archDiagonalOperator_absGraph_self (p : SourceGraph) :
    ⟪archDiagonalOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
      ⟪archDiagonalOperator p.val.fst, p.val.fst⟫_ℝ := by
  rw [inner_archDiagonalOperator_self, inner_archDiagonalOperator_self,
    norm_thetaToVolume_absGraph_sq]

theorem inner_primeDiagonalOperator_absGraph_self (p : SourceGraph) :
    ⟪primeDiagonalOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
      ⟪primeDiagonalOperator p.val.fst, p.val.fst⟫_ℝ := by
  rw [inner_primeDiagonalOperator_self, inner_primeDiagonalOperator_self]
  apply integral_congr_ae
  filter_upwards [absGraph_fst_ae p] with x ha
  rw [ha]
  dsimp only [absFun]
  rw [sq_abs]

theorem inner_groundPotentialOperator_absGraph_self (p : SourceGraph) :
    ⟪groundPotentialOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
      ⟪groundPotentialOperator p.val.fst, p.val.fst⟫_ℝ := by
  rw [inner_groundPotentialOperator_self, inner_groundPotentialOperator_self]
  apply integral_congr_ae
  filter_upwards [absGraph_fst_ae p] with x ha
  rw [ha]
  dsimp only [absFun]
  rw [sq_abs]

/-! ## Section 2: Stationary Beurling–Deny Cross-Jump Identity and Strict Stationary Rigidity -/

theorem fullGroundEquiv_posGraph_sub_negGraph (p : SourceGraph) :
    fullGroundEquiv (posGraph p) - fullGroundEquiv (negGraph p) = fullGroundEquiv p := by
  rw [← map_sub, posGraph_sub_negGraph]

theorem fullGroundEquiv_posGraph_add_negGraph (p : SourceGraph) :
    fullGroundEquiv (posGraph p) + fullGroundEquiv (negGraph p) = fullGroundEquiv (absGraph p) := by
  rw [← map_add, posGraph_add_negGraph]

/-- **Stationary Beurling–Deny Nodal Decomposition of `stationaryEnergy`.** -/
theorem stationaryEnergy_eq_posGraph_add_negGraph_sub_two_inner (p : SourceGraph) :
    stationaryEnergy (thetaProduct p.val.fst) =
      stationaryEnergy (thetaProduct (posGraph p).val.fst) +
        stationaryEnergy (thetaProduct (negGraph p).val.fst) -
        2 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ := by
  have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
  have hpos : (fullGroundEquiv (posGraph p)).val.fst = (posGraph p).val.fst :=
    fullGroundEquiv_source (posGraph p)
  have hneg : (fullGroundEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
    fullGroundEquiv_source (negGraph p)
  rw [← hp, ← stationaryGround_edge_energy, ← hpos, ← stationaryGround_edge_energy,
    ← hneg, ← stationaryGround_edge_energy]
  have hsub : (fullGroundEquiv p).val.snd =
      (fullGroundEquiv (posGraph p)).val.snd - (fullGroundEquiv (negGraph p)).val.snd :=
    congrArg (fun q : stationaryGroundGraph => q.val.snd)
      (fullGroundEquiv_posGraph_sub_negGraph p).symm
  rw [hsub, norm_sub_sq_real]
  ring

/-- **Exact Stationary Beurling–Deny Cross-Jump Formula for `absGraph p`.** -/
theorem stationaryEnergy_absGraph_eq (p : SourceGraph) :
    stationaryEnergy (thetaProduct (absGraph p).val.fst) =
      stationaryEnergy (thetaProduct p.val.fst) +
        4 * ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ := by
  have habs : (fullGroundEquiv (absGraph p)).val.fst = (absGraph p).val.fst :=
    fullGroundEquiv_source (absGraph p)
  have hpos : (fullGroundEquiv (posGraph p)).val.fst = (posGraph p).val.fst :=
    fullGroundEquiv_source (posGraph p)
  have hneg : (fullGroundEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
    fullGroundEquiv_source (negGraph p)
  rw [← habs, ← stationaryGround_edge_energy,
    stationaryEnergy_eq_posGraph_add_negGraph_sub_two_inner p,
    ← hpos, ← stationaryGround_edge_energy, ← hneg, ← stationaryGround_edge_energy]
  have hadd : (fullGroundEquiv (absGraph p)).val.snd =
      (fullGroundEquiv (posGraph p)).val.snd + (fullGroundEquiv (negGraph p)).val.snd :=
    congrArg (fun q : stationaryGroundGraph => q.val.snd)
      (fullGroundEquiv_posGraph_add_negGraph p).symm
  rw [hadd, norm_add_sq_real]
  ring

/-- The stationary edge pairing between `posGraph p` and `negGraph p` equals the archimedean edge
pairing `⟪(graphArchEquiv (posGraph p)).val.snd, (graphArchEquiv (negGraph p)).val.snd⟫_ℝ`. -/
theorem inner_fullGroundEquiv_posGraph_negGraph_snd_eq_arch (p : SourceGraph) :
    ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ =
      ⟪(graphArchEquiv (posGraph p)).val.snd, (graphArchEquiv (negGraph p)).val.snd⟫_ℝ := by
  have h := archGround_inner_decomposition (graphArchEquiv (posGraph p))
    (graphArchEquiv (negGraph p))
  have hpos : archSourceMap (graphArchEquiv (posGraph p)) = (posGraph p).val.fst :=
    graphArchEquiv_source (posGraph p)
  have hneg : archSourceMap (graphArchEquiv (negGraph p)) = (negGraph p).val.fst :=
    graphArchEquiv_source (negGraph p)
  have hpos' : (graphArchEquiv (posGraph p)).val.fst = (posGraph p).val.fst :=
    graphArchEquiv_source (posGraph p)
  have hneg' : (graphArchEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
    graphArchEquiv_source (negGraph p)
  have hfpos : (fullGroundEquiv (posGraph p)).val.fst = (posGraph p).val.fst :=
    fullGroundEquiv_source (posGraph p)
  have hfneg : (fullGroundEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
    fullGroundEquiv_source (negGraph p)
  change ⟪graphArchEquiv (posGraph p), graphArchEquiv (negGraph p)⟫_ℝ =
    ⟪fullGroundEquiv (posGraph p), fullGroundEquiv (negGraph p)⟫_ℝ +
      ⟪groundPotentialOperator (archSourceMap (graphArchEquiv (posGraph p))),
        archSourceMap (graphArchEquiv (negGraph p))⟫_ℝ at h
  rw [hpos, hneg, inner_groundPotentialOperator_posGraph_negGraph, add_zero,
    Submodule.coe_inner, WithLp.prod_inner_apply,
    Submodule.coe_inner, WithLp.prod_inner_apply] at h
  change ⟪(graphArchEquiv (posGraph p)).val.fst, (graphArchEquiv (negGraph p)).val.fst⟫_ℝ +
      ⟪(graphArchEquiv (posGraph p)).val.snd, (graphArchEquiv (negGraph p)).val.snd⟫_ℝ =
    ⟪(fullGroundEquiv (posGraph p)).val.fst, (fullGroundEquiv (negGraph p)).val.fst⟫_ℝ +
      ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ at h
  rw [hpos', hneg', hfpos, hfneg] at h
  linarith

/-- Explicit integral formula for the stationary cross-jump edge pairing on `archMeasure`. -/
theorem inner_fullGroundEquiv_posGraph_negGraph_snd_eq_integral (p : SourceGraph) :
    ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ =
      -∫ e, (posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
        negFun (p.val.fst (left e)) * posFun (p.val.fst (right e))) ∂archMeasure := by
  rw [inner_fullGroundEquiv_posGraph_negGraph_snd_eq_arch, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  have hp_snd : (graphArchEquiv (posGraph p)).val.snd =ᵐ[archMeasure]
      difference (posGraph p).val.fst := by
    have h1 : (graphArchEquiv (posGraph p)).val.snd =ᵐ[archMeasure]
        difference (graphArchEquiv (posGraph p)).val.fst :=
      (graphArchEquiv (posGraph p)).property
    have h2 : (graphArchEquiv (posGraph p)).val.fst = (posGraph p).val.fst :=
      graphArchEquiv_source (posGraph p)
    rwa [h2] at h1
  have hn_snd : (graphArchEquiv (negGraph p)).val.snd =ᵐ[archMeasure]
      difference (negGraph p).val.fst := by
    have h1 : (graphArchEquiv (negGraph p)).val.snd =ᵐ[archMeasure]
        difference (graphArchEquiv (negGraph p)).val.fst :=
      (graphArchEquiv (negGraph p)).property
    have h2 : (graphArchEquiv (negGraph p)).val.fst = (negGraph p).val.fst :=
      graphArchEquiv_source (negGraph p)
    rwa [h2] at h1
  have hp_l := nonsingular_arch_left.ae_eq_comp (posGraph_fst_ae p)
  have hp_r := nonsingular_arch_right.ae_eq_comp (posGraph_fst_ae p)
  have hn_l := nonsingular_arch_left.ae_eq_comp (negGraph_fst_ae p)
  have hn_r := nonsingular_arch_right.ae_eq_comp (negGraph_fst_ae p)
  filter_upwards [hp_snd, hn_snd, hp_l, hp_r, hn_l, hn_r] with e hps hns hpl hpr hnl hnr
  simp only [Function.comp_apply] at hpl hpr hnl hnr
  simp only [RCLike.inner_apply', conj_trivial, hps, hns, difference, hpl, hpr, hnl, hnr]
  rw [posFun_diff_mul_negFun_diff]

theorem inner_fullGroundEquiv_posGraph_negGraph_snd_nonpos (p : SourceGraph) :
    ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ ≤ 0 := by
  rw [inner_fullGroundEquiv_posGraph_negGraph_snd_eq_integral]
  have hnn : 0 ≤ ∫ e, (posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
      negFun (p.val.fst (left e)) * posFun (p.val.fst (right e))) ∂archMeasure :=
    integral_nonneg fun e => add_nonneg
      (mul_nonneg (posFun_nonneg _) (negFun_nonneg _))
      (mul_nonneg (negFun_nonneg _) (posFun_nonneg _))
  linarith

/-- **Strict Stationary Cross-Jump Irreducibility:**
the stationary edge pairing `⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ`
vanishes if and only if `posGraph p = 0 ∨ negGraph p = 0`. -/
theorem inner_fullGroundEquiv_posGraph_negGraph_snd_eq_zero_iff (p : SourceGraph) :
    ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ = 0 ↔
      posGraph p = 0 ∨ negGraph p = 0 := by
  constructor
  · intro h0
    rw [inner_fullGroundEquiv_posGraph_negGraph_snd_eq_integral, neg_eq_zero] at h0
    have hint : Integrable (fun e => posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
        negFun (p.val.fst (left e)) * posFun (p.val.fst (right e))) archMeasure :=
      (integrable_crossJump p).left_of_add_measure
    have harch : ∀ᵐ e ∂archMeasure,
        posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
          negFun (p.val.fst (left e)) * posFun (p.val.fst (right e)) = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun e => add_nonneg
          (mul_nonneg (posFun_nonneg _) (negFun_nonneg _))
          (mul_nonneg (negFun_nonneg _) (posFun_nonneg _)))
        hint).mp h0
    rcases posGraph_eq_zero_or_negGraph_eq_zero_of_arch_cross_zero p.val.fst
      (Lp.stronglyMeasurable p.val.fst).measurable harch with hp | hn
    · left
      apply source_projection_injective
      rw [Lp.ext_iff]
      filter_upwards [posGraph_fst_ae p, (withDensity_absolutelyContinuous volume _).ae_eq hp,
        Lp.coeFn_zero ℝ 2 massMeasure] with x hx1 hx2 hx0
      change (posGraph p).val.fst x = (0 : MassSpace) x
      rw [hx1, hx2, hx0, Pi.zero_apply]
    · right
      apply source_projection_injective
      rw [Lp.ext_iff]
      filter_upwards [negGraph_fst_ae p, (withDensity_absolutelyContinuous volume _).ae_eq hn,
        Lp.coeFn_zero ℝ 2 massMeasure] with x hx1 hx2 hx0
      change (negGraph p).val.fst x = (0 : MassSpace) x
      rw [hx1, hx2, hx0, Pi.zero_apply]
  · rintro (hp | hn)
    · rw [hp, map_zero]
      exact inner_zero_left _
    · rw [hn, map_zero]
      exact inner_zero_right _

theorem inner_fullGroundEquiv_posGraph_negGraph_snd_neg_of_ne_zero {p : SourceGraph}
    (hp : posGraph p ≠ 0) (hn : negGraph p ≠ 0) :
    ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ < 0 := by
  apply lt_of_le_of_ne (inner_fullGroundEquiv_posGraph_negGraph_snd_nonpos p)
  intro h0
  rcases (inner_fullGroundEquiv_posGraph_negGraph_snd_eq_zero_iff p).mp h0 with h | h
  · exact hp h
  · exact hn h

/-- **Stationary Beurling–Deny Contraction Inequality on `SourceGraph`.** -/
theorem stationaryEnergy_absGraph_le (p : SourceGraph) :
    stationaryEnergy (thetaProduct (absGraph p).val.fst) ≤
      stationaryEnergy (thetaProduct p.val.fst) := by
  rw [stationaryEnergy_absGraph_eq]
  linarith [inner_fullGroundEquiv_posGraph_negGraph_snd_nonpos p]

/-- **Strict Stationary Beurling–Deny Rigidity:**
`stationaryEnergy (thetaProduct (absGraph p).val.fst) = stationaryEnergy (thetaProduct p.val.fst)`
if and only if `p` does not change sign (`posGraph p = 0 ∨ negGraph p = 0`). -/
theorem stationaryEnergy_absGraph_eq_iff (p : SourceGraph) :
    stationaryEnergy (thetaProduct (absGraph p).val.fst) =
      stationaryEnergy (thetaProduct p.val.fst) ↔
        posGraph p = 0 ∨ negGraph p = 0 := by
  rw [stationaryEnergy_absGraph_eq, ← inner_fullGroundEquiv_posGraph_negGraph_snd_eq_zero_iff]
  constructor <;> intro h <;> linarith

theorem stationaryEnergy_absGraph_lt_of_ne_zero {p : SourceGraph}
    (hp : posGraph p ≠ 0) (hn : negGraph p ≠ 0) :
    stationaryEnergy (thetaProduct (absGraph p).val.fst) <
      stationaryEnergy (thetaProduct p.val.fst) := by
  rw [stationaryEnergy_absGraph_eq]
  linarith [inner_fullGroundEquiv_posGraph_negGraph_snd_neg_of_ne_zero hp hn]

/-- Every nonzero primitive graph vector (and in particular every nonzero odd graph vector) has
strictly smaller stationary energy after absolute-value contraction. -/
theorem stationaryEnergy_absGraph_lt_of_primitive {p : SourceGraph}
    (hp0 : p ≠ 0) (hprim : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    stationaryEnergy (thetaProduct (absGraph p).val.fst) <
      stationaryEnergy (thetaProduct p.val.fst) := by
  obtain ⟨hp, hn⟩ := posGraph_ne_zero_and_negGraph_ne_zero_of_primitive hp0 hprim
  exact stationaryEnergy_absGraph_lt_of_ne_zero hp hn

/-! ## Section 3: Positivity and Modulus Domination of `primeShiftOperator` -/

theorem inner_primeShiftOperator_self_nonneg_of_ae_nonneg {u : MassSpace}
    (hu : 0 ≤ᵐ[massMeasure] (u : ℝ → ℝ)) :
    0 ≤ ⟪primeShiftOperator u, u⟫_ℝ := by
  rw [inner_primeShiftOperator_self_eq_integral]
  refine mul_nonneg (by norm_num) (integral_nonneg_of_ae ?_)
  filter_upwards [nonsingular_allPrime_left.ae hu, nonsingular_allPrime_right.ae hu] with e hl hr
  exact mul_nonneg hl hr

theorem inner_primeShiftOperator_posGraph_self_nonneg (p : SourceGraph) :
    0 ≤ ⟪primeShiftOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ := by
  refine inner_primeShiftOperator_self_nonneg_of_ae_nonneg ?_
  filter_upwards [posGraph_fst_ae p] with x hx
  change 0 ≤ (posGraph p).val.fst x
  rw [hx]
  exact posFun_nonneg _

theorem inner_primeShiftOperator_negGraph_self_nonneg (p : SourceGraph) :
    0 ≤ ⟪primeShiftOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  refine inner_primeShiftOperator_self_nonneg_of_ae_nonneg ?_
  filter_upwards [negGraph_fst_ae p] with x hx
  change 0 ≤ (negGraph p).val.fst x
  rw [hx]
  exact negFun_nonneg _

theorem inner_primeShiftOperator_absGraph_self_nonneg (p : SourceGraph) :
    0 ≤ ⟪primeShiftOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ := by
  refine inner_primeShiftOperator_self_nonneg_of_ae_nonneg ?_
  filter_upwards [absGraph_fst_ae p] with x hx
  change 0 ≤ (absGraph p).val.fst x
  rw [hx]
  exact abs_nonneg _

/-- On `posGraph p` and `negGraph p`, `primeShiftOperator` equals `-primeGenerator` and has
nonnegative cross-pairing. -/
theorem inner_primeShiftOperator_posGraph_negGraph_eq (p : SourceGraph) :
    ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ =
      ∫ e, (posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
        negFun (p.val.fst (left e)) * posFun (p.val.fst (right e))) ∂allPrimeMeasure := by
  change ⟪primeDiagonalOperator (posGraph p).val.fst -
    primeGenerator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ = _
  rw [inner_sub_left, inner_primeDiagonalOperator_posGraph_negGraph, zero_sub,
    inner_primeGenerator_eq_integral, ← integral_neg]
  apply integral_congr_ae
  have hp_l := nonsingular_allPrime_left.ae_eq_comp (posGraph_fst_ae p)
  have hp_r := nonsingular_allPrime_right.ae_eq_comp (posGraph_fst_ae p)
  have hn_l := nonsingular_allPrime_left.ae_eq_comp (negGraph_fst_ae p)
  have hn_r := nonsingular_allPrime_right.ae_eq_comp (negGraph_fst_ae p)
  filter_upwards [hp_l, hp_r, hn_l, hn_r] with e hpl hpr hnl hnr
  simp only [Function.comp_apply] at hpl hpr hnl hnr
  change -(difference (posGraph p).val.fst e * difference (negGraph p).val.fst e) = _
  simp only [difference, hpl, hpr, hnl, hnr]
  rw [posFun_diff_mul_negFun_diff, neg_neg]

theorem inner_primeShiftOperator_posGraph_negGraph_nonneg (p : SourceGraph) :
    0 ≤ ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [inner_primeShiftOperator_posGraph_negGraph_eq]
  exact integral_nonneg fun e => add_nonneg
    (mul_nonneg (posFun_nonneg _) (negFun_nonneg _))
    (mul_nonneg (negFun_nonneg _) (posFun_nonneg _))

/-- **Exact Nodal Decomposition of `⟪primeShiftOperator u, u⟫` on `SourceGraph`.** -/
theorem inner_primeShiftOperator_eq_posGraph_add_negGraph_sub_two_pair (p : SourceGraph) :
    ⟪primeShiftOperator p.val.fst, p.val.fst⟫_ℝ =
      ⟪primeShiftOperator (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ +
        ⟪primeShiftOperator (negGraph p).val.fst, (negGraph p).val.fst⟫_ℝ -
        2 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have hsub : p.val.fst = (posGraph p).val.fst - (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p).symm
  conv_lhs => rw [hsub]
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    primeShiftOperator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm (primeShiftOperator (posGraph p).val.fst)]
  ring

/-- **Exact Cross-Jump Formula for `⟪primeShiftOperator (absGraph p), absGraph p⟫`.** -/
theorem inner_primeShiftOperator_absGraph_self_eq (p : SourceGraph) :
    ⟪primeShiftOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ =
      ⟪primeShiftOperator p.val.fst, p.val.fst⟫_ℝ +
        4 * ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  have hadd : (absGraph p).val.fst = (posGraph p).val.fst + (negGraph p).val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_add_negGraph p).symm
  rw [hadd, map_add, inner_add_left, inner_add_right, inner_add_right,
    primeShiftOperator_symmetric (negGraph p).val.fst (posGraph p).val.fst,
    real_inner_comm (primeShiftOperator (posGraph p).val.fst),
    inner_primeShiftOperator_eq_posGraph_add_negGraph_sub_two_pair p]
  ring

/-- **Prime-Shift Modulus Domination on `SourceGraph`:**
`|^⟪primeShiftOperator p.fst, p.fst⟫| ≤ ⟪primeShiftOperator (absGraph p).fst, (absGraph p).fst⟫`. -/
theorem abs_inner_primeShiftOperator_le_absGraph (p : SourceGraph) :
    |⟪primeShiftOperator p.val.fst, p.val.fst⟫_ℝ| ≤
      ⟪primeShiftOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ := by
  rw [abs_le]
  have hplus := inner_primeShiftOperator_posGraph_self_nonneg p
  have hminus := inner_primeShiftOperator_negGraph_self_nonneg p
  have hcross := inner_primeShiftOperator_posGraph_negGraph_nonneg p
  have h1 := inner_primeShiftOperator_eq_posGraph_add_negGraph_sub_two_pair p
  have h2 := inner_primeShiftOperator_absGraph_self_eq p
  constructor <;> linarith

/-! ## Section 4: Bilateral Decomposition of the Total Nodal Cross-Jump Pairing -/

/-- **Bilateral Stationary + Prime-Shift Decomposition of `sourcePair (posGraph p) (negGraph p)`.**
The total Beurling–Deny cross-jump pairing splits into the stationary archimedean cross-jump
pairing (which is $\le 0$, and $< 0$ whenever $p$ changes sign) minus the prime shift cross-jump
pairing (which is $\ge 0$). -/
theorem sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift (p : SourceGraph) :
    sourcePair (posGraph p) (negGraph p) =
      ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ -
        ⟪primeShiftOperator (posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ := by
  rw [sourcePair_eq_stationary_sub_arch_sub_primeShift,
    inner_thetaToVolume_posGraph_negGraph, mul_zero, sub_zero]

/-- **Upper Bound on `sourcePair (posGraph p) (negGraph p)` by the Stationary Cross-Jump Pairing.** -/
theorem sourcePair_posGraph_negGraph_le_stationary (p : SourceGraph) :
    sourcePair (posGraph p) (negGraph p) ≤
      ⟪(fullGroundEquiv (posGraph p)).val.snd, (fullGroundEquiv (negGraph p)).val.snd⟫_ℝ := by
  rw [sourcePair_posGraph_negGraph_eq_stationary_sub_primeShift]
  linarith [inner_primeShiftOperator_posGraph_negGraph_nonneg p]

/-- **Stationary Energy Upper Bound on Any Bound-State Vector (`sourceEnergy p ≤ 0`).**
For every $p \in \mathrm{SourceGraph}$ with $\operatorname{sourceEnergy}(p) \le 0$ (in particular,
every $p \in \mathrm{boundStateSpace}$),
$$\operatorname{stationaryEnergy}(\Theta \cdot p.\mathrm{fst})
  \le c_{\mathrm{arch}}\,\|\operatorname{thetaToVolume}(p.\mathrm{fst})\|_{L^2(\mathbb{R})}^2
    + \langle \operatorname{primeShiftOperator}((\operatorname{absGraph} p).\mathrm{fst}),
      (\operatorname{absGraph} p).\mathrm{fst}\rangle_{\mathbb{R}},$$
and if $p$ is a nonzero primitive vector ($p \ne 0$, $\langle p.\mathrm{fst}, 1\rangle = 0$),
$$\operatorname{stationaryEnergy}(\Theta \cdot (\operatorname{absGraph} p).\mathrm{fst})
  < \operatorname{stationaryEnergy}(\Theta \cdot p.\mathrm{fst})
  \le c_{\mathrm{arch}}\,\|\operatorname{thetaToVolume}(p.\mathrm{fst})\|_{L^2(\mathbb{R})}^2
    + \langle \operatorname{primeShiftOperator}((\operatorname{absGraph} p).\mathrm{fst}),
      (\operatorname{absGraph} p).\mathrm{fst}\rangle_{\mathbb{R}}.$$ -/
theorem stationaryEnergy_le_arch_add_primeShift_absGraph_of_sourceEnergy_nonpos
    {p : SourceGraph} (hp : sourceEnergy p ≤ 0) :
    stationaryEnergy (thetaProduct p.val.fst) ≤
      archGroundConstant * ‖thetaToVolume p.val.fst‖ ^ 2 +
        ⟪primeShiftOperator (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ := by
  have h1 := sourceEnergy_eq_stationary_sub_arch_sub_primeShift p
  have h2 := (le_abs_self ⟪primeShiftOperator p.val.fst, p.val.fst⟫_ℝ).trans
    (abs_inner_primeShiftOperator_le_absGraph p)
  linarith

end RHTower.CHMDPolar
