import GaloisForLFunctions.RHTower.PrimeIsingTreeBalancedVarianceRankNoGo
import GaloisForLFunctions.RHTower.XiHypertranscendenceUnconditional
import GaloisForLFunctions.HTGeometry.FixedModalLocallyUniformHankel
import GaloisForLFunctions.HTGeometry.ExponentialSumDA
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance

/-!
# Fixed-modal closure obstruction for balanced prime Ising trees

Every finite prime Ising tree has an exact spin spectral packet with one exponential line per
spin configuration.  Its balanced partition therefore has modal width exactly bounded by
`2 ^ |V|` at every derivative jet and every observation point.  Combining this exact packet law
with the source curvature floor and completed-xi hypertranscendence excludes locally-uniform
convergence of *every* sequence of balanced finite trees to the pointed completed Xi function.
-/

open Complex Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- One complex exponential line `amplitude * exp(frequency * z)`. -/
structure PrimeIsingSpectralLine where
  amplitude : ℂ
  frequency : ℂ

/-- Evaluation of a finite spectral packet. -/
def primeIsingSpectralPacketEval
    (packet : List PrimeIsingSpectralLine) (z : ℂ) : ℂ :=
  (packet.map fun line => line.amplitude * Complex.exp (line.frequency * z)).sum

/-- Multiply every line amplitude by a scalar. -/
def PrimeIsingSpectralLine.scalePacket
    (c : ℂ) (packet : List PrimeIsingSpectralLine) : List PrimeIsingSpectralLine :=
  packet.map fun line => ⟨c * line.amplitude, line.frequency⟩

/-- Add one common frequency to every line. -/
def PrimeIsingSpectralLine.shiftPacket
    (r : ℂ) (packet : List PrimeIsingSpectralLine) : List PrimeIsingSpectralLine :=
  packet.map fun line => ⟨line.amplitude, r + line.frequency⟩

/-- Cauchy product of two finite spectral packets. -/
def PrimeIsingSpectralLine.mulPacket
    (left right : List PrimeIsingSpectralLine) : List PrimeIsingSpectralLine :=
  left.flatMap fun x =>
    right.map fun y => ⟨x.amplitude * y.amplitude, x.frequency + y.frequency⟩

/-- Unit packet. -/
def PrimeIsingSpectralLine.onePacket : List PrimeIsingSpectralLine :=
  [⟨1, 0⟩]

@[simp] theorem primeIsingSpectralPacketEval_nil (z : ℂ) :
    primeIsingSpectralPacketEval [] z = 0 := rfl

@[simp] theorem primeIsingSpectralPacketEval_cons
    (line : PrimeIsingSpectralLine) (packet : List PrimeIsingSpectralLine) (z : ℂ) :
    primeIsingSpectralPacketEval (line :: packet) z =
      line.amplitude * Complex.exp (line.frequency * z) +
        primeIsingSpectralPacketEval packet z := by
  simp [primeIsingSpectralPacketEval]

@[simp] theorem primeIsingSpectralPacketEval_onePacket (z : ℂ) :
    primeIsingSpectralPacketEval PrimeIsingSpectralLine.onePacket z = 1 := by
  simp [primeIsingSpectralPacketEval, PrimeIsingSpectralLine.onePacket]

theorem primeIsingSpectralPacketEval_append
    (left right : List PrimeIsingSpectralLine) (z : ℂ) :
    primeIsingSpectralPacketEval (left ++ right) z =
      primeIsingSpectralPacketEval left z + primeIsingSpectralPacketEval right z := by
  simp [primeIsingSpectralPacketEval, List.sum_append]

theorem primeIsingSpectralPacketEval_scalePacket
    (c : ℂ) (packet : List PrimeIsingSpectralLine) (z : ℂ) :
    primeIsingSpectralPacketEval (PrimeIsingSpectralLine.scalePacket c packet) z =
      c * primeIsingSpectralPacketEval packet z := by
  induction packet with
  | nil => simp [PrimeIsingSpectralLine.scalePacket]
  | cons line tail ih =>
      simp only [PrimeIsingSpectralLine.scalePacket, List.map_cons,
        primeIsingSpectralPacketEval_cons]
      change c * line.amplitude * Complex.exp (line.frequency * z) +
          primeIsingSpectralPacketEval
            (PrimeIsingSpectralLine.scalePacket c tail) z =
        c * (line.amplitude * Complex.exp (line.frequency * z) +
          primeIsingSpectralPacketEval tail z)
      rw [ih]
      ring

theorem primeIsingSpectralPacketEval_shiftPacket
    (r : ℂ) (packet : List PrimeIsingSpectralLine) (z : ℂ) :
    primeIsingSpectralPacketEval (PrimeIsingSpectralLine.shiftPacket r packet) z =
      Complex.exp (r * z) * primeIsingSpectralPacketEval packet z := by
  induction packet with
  | nil => simp [PrimeIsingSpectralLine.shiftPacket]
  | cons line tail ih =>
      simp only [PrimeIsingSpectralLine.shiftPacket, List.map_cons,
        primeIsingSpectralPacketEval_cons]
      rw [show (r + line.frequency) * z = r * z + line.frequency * z by ring,
        Complex.exp_add]
      change line.amplitude *
            (Complex.exp (r * z) * Complex.exp (line.frequency * z)) +
          primeIsingSpectralPacketEval
            (PrimeIsingSpectralLine.shiftPacket r tail) z =
        Complex.exp (r * z) *
          (line.amplitude * Complex.exp (line.frequency * z) +
            primeIsingSpectralPacketEval tail z)
      rw [ih]
      ring

private theorem primeIsingSpectralPacketEval_mulLinePacket
    (line : PrimeIsingSpectralLine) (packet : List PrimeIsingSpectralLine) (z : ℂ) :
    primeIsingSpectralPacketEval
        (packet.map fun y =>
          ⟨line.amplitude * y.amplitude, line.frequency + y.frequency⟩) z =
      line.amplitude * Complex.exp (line.frequency * z) *
        primeIsingSpectralPacketEval packet z := by
  induction packet with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, primeIsingSpectralPacketEval_cons]
      rw [show (line.frequency + y.frequency) * z =
          line.frequency * z + y.frequency * z by ring,
        Complex.exp_add, ih]
      ring

theorem primeIsingSpectralPacketEval_mulPacket
    (left right : List PrimeIsingSpectralLine) (z : ℂ) :
    primeIsingSpectralPacketEval (PrimeIsingSpectralLine.mulPacket left right) z =
      primeIsingSpectralPacketEval left z * primeIsingSpectralPacketEval right z := by
  induction left with
  | nil => simp [PrimeIsingSpectralLine.mulPacket]
  | cons line tail ih =>
      change primeIsingSpectralPacketEval
          ((right.map fun y =>
              ⟨line.amplitude * y.amplitude, line.frequency + y.frequency⟩) ++
            PrimeIsingSpectralLine.mulPacket tail right) z = _
      rw [primeIsingSpectralPacketEval_append,
        primeIsingSpectralPacketEval_mulLinePacket, ih,
        primeIsingSpectralPacketEval_cons]
      ring

@[simp] theorem length_scalePacket (c : ℂ) (packet : List PrimeIsingSpectralLine) :
    (PrimeIsingSpectralLine.scalePacket c packet).length = packet.length := by
  simp [PrimeIsingSpectralLine.scalePacket]

@[simp] theorem length_shiftPacket (r : ℂ) (packet : List PrimeIsingSpectralLine) :
    (PrimeIsingSpectralLine.shiftPacket r packet).length = packet.length := by
  simp [PrimeIsingSpectralLine.shiftPacket]

@[simp] theorem length_mulPacket (left right : List PrimeIsingSpectralLine) :
    (PrimeIsingSpectralLine.mulPacket left right).length = left.length * right.length := by
  induction left with
  | nil => simp [PrimeIsingSpectralLine.mulPacket]
  | cons line tail ih =>
      simp [PrimeIsingSpectralLine.mulPacket, Nat.add_mul, Nat.add_comm]

mutual
  /-- Exact spectral packets for the two root-spin conditional weights. -/
  def treeConditionalSpectralPackets :
      PrimeIsingTree → List PrimeIsingSpectralLine × List PrimeIsingSpectralLine
    | .node p branches =>
        let factors := forestConditionalSpectralPackets branches
        (factors.1,
          PrimeIsingSpectralLine.shiftPacket
            (-((_root_.RHTower.primeLeeYangLog p : ℝ) : ℂ) * I) factors.2)

  /-- Exact spectral packets for the two parent-spin forest factors. -/
  def forestConditionalSpectralPackets :
      PrimeIsingForest → List PrimeIsingSpectralLine × List PrimeIsingSpectralLine
    | .nil =>
        (PrimeIsingSpectralLine.onePacket, PrimeIsingSpectralLine.onePacket)
    | .cons coupling child tail =>
        let childPackets := treeConditionalSpectralPackets child
        let tailPackets := forestConditionalSpectralPackets tail
        (PrimeIsingSpectralLine.mulPacket
            (childPackets.1 ++
              PrimeIsingSpectralLine.scalePacket
                (coupling.coefficient : ℂ) childPackets.2)
            tailPackets.1,
          PrimeIsingSpectralLine.mulPacket
            (PrimeIsingSpectralLine.scalePacket
                (coupling.coefficient : ℂ) childPackets.1 ++ childPackets.2)
            tailPackets.2)
end

mutual
  /-- Packet evaluation recovers both conditional tree weights exactly. -/
  theorem eval_treeConditionalSpectralPackets
      (T : PrimeIsingTree) (z : ℂ) :
      (primeIsingSpectralPacketEval (treeConditionalSpectralPackets T).1 z,
          primeIsingSpectralPacketEval (treeConditionalSpectralPackets T).2 z) =
        treeConditionalWeights
          (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T := by
    cases T with
    | node p branches =>
        have hf := eval_forestConditionalSpectralPackets branches z
        have hf1 := congrArg Prod.fst hf
        have hf2 := congrArg Prod.snd hf
        simp only [treeConditionalSpectralPackets, treeConditionalWeights] at hf1 hf2 ⊢
        apply Prod.ext
        · exact hf1
        · rw [primeIsingSpectralPacketEval_shiftPacket,
            centeredPrimeLeeYangField_eq_massExp, hf2]

  /-- Packet evaluation recovers both conditional forest factors exactly. -/
  theorem eval_forestConditionalSpectralPackets
      (F : PrimeIsingForest) (z : ℂ) :
      (primeIsingSpectralPacketEval (forestConditionalSpectralPackets F).1 z,
          primeIsingSpectralPacketEval (forestConditionalSpectralPackets F).2 z) =
        forestConditionalFactors
          (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) F := by
    cases F with
    | nil =>
        simp [forestConditionalSpectralPackets, forestConditionalFactors]
    | cons coupling child tail =>
        have ht := eval_treeConditionalSpectralPackets child z
        have hf := eval_forestConditionalSpectralPackets tail z
        have ht1 := congrArg Prod.fst ht
        have ht2 := congrArg Prod.snd ht
        have hf1 := congrArg Prod.fst hf
        have hf2 := congrArg Prod.snd hf
        simp only [forestConditionalSpectralPackets, forestConditionalFactors]
          at ht1 ht2 hf1 hf2 ⊢
        apply Prod.ext
        · change primeIsingSpectralPacketEval
              (PrimeIsingSpectralLine.mulPacket
                ((treeConditionalSpectralPackets child).1 ++
                  PrimeIsingSpectralLine.scalePacket (coupling.coefficient : ℂ)
                    (treeConditionalSpectralPackets child).2)
                (forestConditionalSpectralPackets tail).1) z =
              ((treeConditionalWeights
                    (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) child).1 +
                (coupling.coefficient : ℂ) *
                  (treeConditionalWeights
                    (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) child).2) *
                (forestConditionalFactors
                  (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) tail).1
          rw [primeIsingSpectralPacketEval_mulPacket,
            primeIsingSpectralPacketEval_append,
            primeIsingSpectralPacketEval_scalePacket,
            ht1, ht2, hf1]
        · change primeIsingSpectralPacketEval
              (PrimeIsingSpectralLine.mulPacket
                (PrimeIsingSpectralLine.scalePacket (coupling.coefficient : ℂ)
                    (treeConditionalSpectralPackets child).1 ++
                  (treeConditionalSpectralPackets child).2)
                (forestConditionalSpectralPackets tail).2) z =
              ((coupling.coefficient : ℂ) *
                  (treeConditionalWeights
                    (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) child).1 +
                (treeConditionalWeights
                  (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) child).2) *
                (forestConditionalFactors
                  (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) tail).2
          rw [primeIsingSpectralPacketEval_mulPacket,
            primeIsingSpectralPacketEval_append,
            primeIsingSpectralPacketEval_scalePacket,
            ht1, ht2, hf2]
end

/-- Full spin spectral packet of a finite prime Ising tree. -/
def primeIsingTreeSpectralPacket (T : PrimeIsingTree) : List PrimeIsingSpectralLine :=
  (treeConditionalSpectralPackets T).1 ++ (treeConditionalSpectralPackets T).2

/-- Exact packet representation of the unnormalized finite-tree partition. -/
theorem primeIsingTreePartition_eq_spectralPacketEval
    (T : PrimeIsingTree) (z : ℂ) :
    primeIsingTreePartition T z =
      primeIsingSpectralPacketEval (primeIsingTreeSpectralPacket T) z := by
  have h := eval_treeConditionalSpectralPackets T z
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change primeIsingSpectralPacketEval (treeConditionalSpectralPackets T).1 z =
    (treeConditionalWeights
      (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T).1 at h1
  change primeIsingSpectralPacketEval (treeConditionalSpectralPackets T).2 z =
    (treeConditionalWeights
      (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T).2 at h2
  rw [primeIsingTreePartition, treePartition, primeIsingTreeSpectralPacket,
    primeIsingSpectralPacketEval_append]
  rw [h1, h2]

mutual
  /-- The two root-spin packets contain exactly one line per spin configuration. -/
  theorem length_treeConditionalSpectralPackets (T : PrimeIsingTree) :
      (treeConditionalSpectralPackets T).1.length +
          (treeConditionalSpectralPackets T).2.length =
        2 ^ primeIsingTreeVertexCount T := by
    cases T with
    | node p branches =>
        have hf := length_forestConditionalSpectralPackets branches
        simp only [treeConditionalSpectralPackets, primeIsingTreeVertexCount,
          length_shiftPacket]
        rw [hf.1, hf.2]
        rw [show 1 + primeIsingForestVertexCount branches =
            primeIsingForestVertexCount branches + 1 by omega, pow_succ]
        ring

  /-- Each fixed parent-spin forest packet has one line per child-spin configuration. -/
  theorem length_forestConditionalSpectralPackets (F : PrimeIsingForest) :
      (forestConditionalSpectralPackets F).1.length =
          2 ^ primeIsingForestVertexCount F ∧
        (forestConditionalSpectralPackets F).2.length =
          2 ^ primeIsingForestVertexCount F := by
    cases F with
    | nil =>
        simp [forestConditionalSpectralPackets, primeIsingForestVertexCount,
          PrimeIsingSpectralLine.onePacket]
    | cons coupling child tail =>
        have ht := length_treeConditionalSpectralPackets child
        have hf := length_forestConditionalSpectralPackets tail
        simp only [forestConditionalSpectralPackets, primeIsingForestVertexCount,
          length_mulPacket, List.length_append, length_scalePacket]
        constructor
        · rw [ht, hf.1, pow_add]
        · rw [ht, hf.2, pow_add]
end

/-- Exact cardinality of the full spin packet. -/
theorem length_primeIsingTreeSpectralPacket (T : PrimeIsingTree) :
    (primeIsingTreeSpectralPacket T).length = 2 ^ primeIsingTreeVertexCount T := by
  rw [primeIsingTreeSpectralPacket, List.length_append]
  exact length_treeConditionalSpectralPackets T

/-- Exact spectral packet after the forced half-cocycle and central normalization. -/
def balancedPrimeIsingTreeSpectralPacket
    (T : PrimeIsingTree) : List PrimeIsingSpectralLine :=
  PrimeIsingSpectralLine.shiftPacket
    (((treePrimeLeeYangMass T : ℝ) : ℂ) * I / 2)
    (PrimeIsingSpectralLine.scalePacket (primeIsingTreePartition T 0)⁻¹
      (primeIsingTreeSpectralPacket T))

/-- Exact packet representation of the balanced finite-tree partition. -/
theorem balancedPrimeIsingTreePartition_eq_spectralPacketEval
    (T : PrimeIsingTree) :
    balancedPrimeIsingTreePartition T =
      primeIsingSpectralPacketEval (balancedPrimeIsingTreeSpectralPacket T) := by
  funext z
  rw [balancedPrimeIsingTreeSpectralPacket,
    primeIsingSpectralPacketEval_shiftPacket,
    primeIsingSpectralPacketEval_scalePacket,
    ← primeIsingTreePartition_eq_spectralPacketEval]
  unfold balancedPrimeIsingTreePartition centralNormalizedPrimeIsingTreePartition
  rw [show ((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z / 2 =
      ((treePrimeLeeYangMass T : ℝ) : ℂ) * I / 2 * z by ring]

/-- Balancing and central normalization do not change packet cardinality. -/
theorem length_balancedPrimeIsingTreeSpectralPacket (T : PrimeIsingTree) :
    (balancedPrimeIsingTreeSpectralPacket T).length =
      2 ^ primeIsingTreeVertexCount T := by
  rw [balancedPrimeIsingTreeSpectralPacket, length_shiftPacket,
    length_scalePacket, length_primeIsingTreeSpectralPacket]

/-- A list packet is the corresponding sum over its canonical finite index type. -/
theorem primeIsingSpectralPacketEval_eq_fin_sum
    (packet : List PrimeIsingSpectralLine) :
    primeIsingSpectralPacketEval packet = fun z =>
      ∑ i : Fin packet.length,
        (packet.get i).amplitude * Complex.exp ((packet.get i).frequency * z) := by
  funext z
  unfold primeIsingSpectralPacketEval
  conv_lhs => rw [← List.ofFn_get packet]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- At every point, all derivative jets of a packet have modal width at most its line count. -/
theorem finiteModalWidthAtMost_iteratedDeriv_primeIsingSpectralPacketEval
    (packet : List PrimeIsingSpectralLine) (z : ℂ) :
    HTGeometry.FiniteModalWidthAtMost packet.length
      (fun k => iteratedDeriv k (primeIsingSpectralPacketEval packet) z) := by
  refine ⟨fun i =>
      (packet.get i).amplitude * Complex.exp ((packet.get i).frequency * z),
    fun i => (packet.get i).frequency, ?_⟩
  funext k
  rw [primeIsingSpectralPacketEval_eq_fin_sum]
  rw [GaloisForLFunctions.iteratedDeriv_finset_expSum
    (Finset.univ : Finset (Fin packet.length))
    (fun i => (packet.get i).amplitude)
    (fun i => (packet.get i).frequency) k z]
  simp only [HTGeometry.finiteModalSequence]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact universal jet-width bound for a balanced finite prime Ising tree. -/
theorem finiteModalWidthAtMost_iteratedDeriv_balancedPrimeIsingTreePartition
    (T : PrimeIsingTree) (z : ℂ) :
    HTGeometry.FiniteModalWidthAtMost (2 ^ primeIsingTreeVertexCount T)
      (fun k => iteratedDeriv k (balancedPrimeIsingTreePartition T) z) := by
  rw [balancedPrimeIsingTreePartition_eq_spectralPacketEval]
  rw [← length_balancedPrimeIsingTreeSpectralPacket T]
  exact finiteModalWidthAtMost_iteratedDeriv_primeIsingSpectralPacketEval
    (balancedPrimeIsingTreeSpectralPacket T) z

/-- Hypertranscendence survives the affine critical-line rotation from `xi` to `XiC`. -/
theorem XiC_hypertranscendental :
    GaloisForLFunctions.Hypertranscendental _root_.RHTower.XiC := by
  let shiftedXi : ℂ → ℂ := fun z => _root_.RHTower.xi (z + 1 / 2)
  have hshifted : GaloisForLFunctions.Hypertranscendental shiftedXi := by
    exact (GaloisForLFunctions.hypertranscendental_comp_add_const_iff
      (f := _root_.RHTower.xi) (1 / 2)).2 _root_.RHTower.xi_hypertranscendental
  have hsmooth : ContDiff ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) shiftedXi := by
    exact _root_.RHTower.xi_differentiable.contDiff.comp
      (contDiff_id.add contDiff_const)
  have hrotated : GaloisForLFunctions.Hypertranscendental
      (fun z => shiftedXi (I * z)) :=
    (GaloisForLFunctions.hypertranscendental_comp_const_mul_iff
      hsmooth I_ne_zero).2 hshifted
  have hfun : (fun z => shiftedXi (I * z)) = _root_.RHTower.XiC := by
    funext z
    unfold shiftedXi _root_.RHTower.XiC
    congr 1
    ring
  rwa [hfun] at hrotated

/-- The nonzero unit-central value scaling preserves completed-Xi hypertranscendence. -/
theorem unitCentralXiC_hypertranscendental :
    GaloisForLFunctions.Hypertranscendental unitCentralXiC := by
  exact (GaloisForLFunctions.hypertranscendental_const_mul_iff
    (inv_ne_zero _root_.RHTower.XiC_zero_ne)).2 XiC_hypertranscendental

/-- **Balanced finite-tree CCM source no-go.**  No sequence of finite prime-labelled
ferromagnetic Ising trees, with arbitrary changing labels, couplings, topology, and size, can
converge locally uniformly to the unit-pointed completed Xi function after the source-forced
balancing. -/
theorem not_tendstoLocallyUniformly_balancedPrimeIsingTreePartition_unitCentralXiC
    (T : ℕ → PrimeIsingTree) :
    ¬ TendstoLocallyUniformly
      (fun n => balancedPrimeIsingTreePartition (T n)) unitCentralXiC atTop := by
  intro hconv
  obtain ⟨V, hV⟩ :=
    eventually_vertexCount_nat_bounded_of_balanced_tendstoLocallyUniformly T hconv
  have hwidth : ∀ᶠ n in atTop, ∀ z,
      HTGeometry.FiniteModalWidthAtMost (2 ^ V)
        (fun k => iteratedDeriv k (balancedPrimeIsingTreePartition (T n)) z) := by
    filter_upwards [hV] with n hn
    intro z
    exact (finiteModalWidthAtMost_iteratedDeriv_balancedPrimeIsingTreePartition
      (T n) z).mono (Nat.pow_le_pow_right (by omega) hn)
  exact (HTGeometry.not_tendstoLocallyUniformly_of_hypertranscendental_of_fixedModalJetWidth
    (fun n => differentiable_balancedPrimeIsingTreePartition (T n))
    unitCentralXiC_hypertranscendental hwidth) hconv

end

end GaloisForLFunctions.RHTower
