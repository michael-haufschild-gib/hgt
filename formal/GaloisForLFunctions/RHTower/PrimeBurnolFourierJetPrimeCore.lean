import GaloisForLFunctions.RHTower.PrimeBurnolFourierCompletion
import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetKernel
import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetClosure

/-!
# Literal prime-depth core of the even Fourier–jet graph

For each individual prime, the actual depth columns form a core for maximal multiplication
by position square on even physical L2. Integer Laplace moment determinacy proves density
of the resolvent-weighted columns; the exact even-extension normalization retains every
Euler amplitude. A bounded positive resolvent parametrizes the entire multiplication graph.

The actual two-coordinate Fourier–jet source consequently has the same graph closure on
finite prime-depth inputs as on all even maximal-domain inputs. Bounded first-coordinate
recovery is impossible even on this literal finite source core. No Gamma–Xi identification,
Hardy-index comparison, sub-unit action, or RH proof is asserted.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace LinearPMap
open GaloisForLFunctions.HTGeometry
open HTGeometry
noncomputable section
namespace RHTower

private def weightedDepthFun (p : Nat.Primes) (n : ℕ) (r : ℝ) : ℂ :=
  (1 + (r : ℂ)^2) * burnolDepthFeature (primeBurnolLogRate p) n r

private def weightedDepth (p : Nat.Primes) (n : ℕ) : primeBurnolHalfLineL2 :=
  (primeBurnolAmplitude (p,n))⁻¹ •
    (primeBurnolWindowFeatureLp (p,n) 0 + primeBurnolRadialJetLp (p,n) 2)

private theorem radial_square (pe : Nat.Primes × ℕ) (r : ℝ) :
    primeBurnolRadialJet pe 2 r = (r : ℂ)^2 * primeBurnolWindowFeature pe 0 r := by
  simp only [primeBurnolRadialJet, primeBurnolWindowFeature, primeBurnolComplexExponent,
    Complex.ofReal_zero, mul_zero, add_zero]
  ring

private theorem weightedDepth_ae (p : Nat.Primes) (n : ℕ) :
    (weightedDepth p n : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] weightedDepthFun p n := by
  filter_upwards [Lp.coeFn_smul (primeBurnolAmplitude (p,n))⁻¹
    (primeBurnolWindowFeatureLp (p,n) 0 + primeBurnolRadialJetLp (p,n) 2),
    Lp.coeFn_add (primeBurnolWindowFeatureLp (p,n) 0) (primeBurnolRadialJetLp (p,n) 2),
    primeBurnolWindowFeatureLp_coeFn (p,n) 0,
    primeBurnolRadialJetLp_coeFn (p,n) 2] with r hs ha hf hj
  change ((primeBurnolAmplitude (p,n))⁻¹ •
    (primeBurnolWindowFeatureLp (p,n) 0 + primeBurnolRadialJetLp (p,n) 2)) r = _
  rw [hs, Pi.smul_apply, smul_eq_mul, ha, Pi.add_apply, hf, hj,
    radial_square, primeBurnolWindowFeature_zero_eq_depth]
  dsimp only [weightedDepthFun, primeBurnolLogRate]
  rw [show primeBurnolAmplitude (p,n) * burnolDepthFeature (Real.log (p : ℝ)) n r +
      (r : ℂ)^2 * (primeBurnolAmplitude (p,n) * burnolDepthFeature (Real.log (p : ℝ)) n r) =
      primeBurnolAmplitude (p,n) * ((1+(r : ℂ)^2) * burnolDepthFeature (Real.log (p : ℝ)) n r)
      by ring, ← mul_assoc, inv_mul_cancel₀ (primeBurnolAmplitude_ne_zero (p,n)), one_mul]

private theorem weightedDepthFun_coord (p : Nat.Primes) (n : ℕ) (r : ℝ) :
    weightedDepthFun p n r = (Real.exp (-(primeBurnolLogRate p : ℝ)*r) : ℂ)^n *
      weightedDepthFun p 0 r := by
  unfold weightedDepthFun
  rw [burnolDepthFeature_eq_coordinate_pow (primeBurnolLogRate p) n]
  ring

private theorem weightedDepthFun_real (p : Nat.Primes) (n : ℕ) (r : ℝ) :
    starRingEnd ℂ (weightedDepthFun p n r) = weightedDepthFun p n r := by
  simp only [weightedDepthFun, burnolDepthFeature, map_mul, map_add, map_pow, map_one,
    Complex.conj_ofReal]

private theorem weightedDepthFun_tail_coord (p : Nat.Primes) (N n : ℕ) (r : ℝ) :
    weightedDepthFun p (n+N) r = (Real.exp (-(primeBurnolLogRate p : ℝ)*r) : ℂ)^n *
      weightedDepthFun p N r := by
  rw [weightedDepthFun_coord p (n+N),weightedDepthFun_coord p N,pow_add]
  ring

private theorem dense_weightedDepth (p : Nat.Primes) (N : ℕ := 0) :
    Dense (Submodule.span ℂ (Set.range (fun n => weightedDepth p (n+N))) :
      Set primeBurnolHalfLineL2) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  refine (Submodule.eq_bot_iff _).mpr fun g hg => ?_
  have hmom (n : ℕ) : ∫ r in Ioi (0 : ℝ),
      (Real.exp (-(primeBurnolLogRate p : ℝ)*r) : ℂ)^n *
        (weightedDepthFun p N r * g r) = 0 := by
    have h := (Submodule.mem_orthogonal _ g).mp hg (weightedDepth p (n+N))
      (Submodule.subset_span ⟨n, rfl⟩)
    rw [L2.inner_def] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [weightedDepth_ae p (n+N)] with r hr
    rw [hr, RCLike.inner_apply, weightedDepthFun_real, weightedDepthFun_tail_coord p N n r]
    ring
  have hmem : MemLp (weightedDepthFun p N) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    (memLp_congr_ae (weightedDepth_ae p N)).mp (Lp.memLp (weightedDepth p N))
  have hzero := ae_eq_zero_of_integer_laplace_moments (primeBurnolLogRate p).property
    (hmem.integrable_mul (Lp.memLp g)) hmom
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioi] with r hr hp
  have hbase : burnolDepthFeature (primeBurnolLogRate p) N r ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (ne_of_gt hp) (Real.exp_ne_zero _))
  have hweight : 1 + (r : ℂ)^2 ≠ 0 := by
    have h : (1 + r^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    exact_mod_cast h
  exact (mul_eq_zero.mp hr).resolve_left (mul_ne_zero hweight hbase)


/-- Position-square multiplication preserves the actual even maximal domain. -/
theorem burnolSquarePosition_mem_evenSubspace (f : burnolSquarePosition.domain)
    (hf : (f : SoninL2) ∈ evenSubspace) : burnolSquarePosition f ∈ evenSubspace := by
  have he := l2Reflection_ae (f : SoninL2)
  rw [(mem_evenSubspace_iff _).mp hf] at he
  have hm := maximalRealL2Mul_apply_ae volume (fun x : ℝ => x^2) f
  have hn := hm.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  apply (mem_evenSubspace_iff _).mpr
  apply Lp.ext
  filter_upwards [l2Reflection_ae (burnolSquarePosition f), hm, hn, he] with x hr hm hn he
  change (burnolSquarePosition f) x = ((x^2 : ℝ) : ℂ) * (f : SoninL2) x at hm
  change (burnolSquarePosition f) (-x) = (((-x)^2 : ℝ) : ℂ) * (f : SoninL2) (-x) at hn
  rw [hr, hn, hm, ← he, neg_sq]

private def evenWeightedColumn (pe : Nat.Primes × ℕ) : evenSubspace :=
  ⟨primeBurnolEvenFeatureLp pe + burnolSquarePosition (primeBurnolSquareColumn pe),
    evenSubspace.add_mem (primeBurnolEvenFeatureLp_mem_evenSubspace pe)
      (burnolSquarePosition_mem_evenSubspace _ (primeBurnolEvenFeatureLp_mem_evenSubspace pe))⟩

private theorem evenWeightedColumn_extension (p : Nat.Primes) (n : ℕ) :
    evenWeightedColumn (p,n) = ((Real.sqrt 2 : ℂ) * primeBurnolAmplitude (p,n)) •
      primeBurnolEvenExtension (weightedDepth p n) := by
  apply logEvenUnitary.injective
  rw [map_smul]
  change logEvenUnitary (evenWeightedColumn (p,n)) = _ •
    logEvenUnitary (logEvenUnitary.symm (halfLineExpUnitary (weightedDepth p n)))
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  have hpull := realExp_quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioi).mp (weightedDepth_ae p n))
  have hraw := realExp_quasiMeasurePreserving.ae (primeBurnolEvenFeatureLp_coeFn (p,n))
  have hjet := realExp_quasiMeasurePreserving.ae
    (burnolSquarePosition_primeBurnolSquareColumn (p,n))
  have hadd := realExp_quasiMeasurePreserving.ae
    (Lp.coeFn_add (primeBurnolEvenFeatureLp (p,n)) (burnolSquarePosition (primeBurnolSquareColumn (p,n))))
  filter_upwards [logEvenUnitary_ae (evenWeightedColumn (p,n)),
    Lp.coeFn_smul ((Real.sqrt 2 : ℂ) * primeBurnolAmplitude (p,n))
      (halfLineExpUnitary (weightedDepth p n)),
    halfLineExpUnitary_ae (weightedDepth p n), hpull, hraw, hjet, hadd]
      with t hl hs hh hp hf hj ha
  have hp' := hp (Real.exp_pos t)
  rw [hl, hs, Pi.smul_apply, hh, smul_eq_mul, hp']
  change ((Real.sqrt 2 * Real.exp (t/2) : ℝ) : ℂ) *
    (primeBurnolEvenFeatureLp (p,n) + burnolSquarePosition (primeBurnolSquareColumn (p,n)))
      (Real.exp t) = _
  rw [ha, Pi.add_apply, hf, hj, primeBurnolEvenFeature, abs_of_pos (Real.exp_pos t),
    radial_square, primeBurnolWindowFeature_zero_eq_depth]
  have hsqrt : Real.sqrt (Real.exp t) = Real.exp (t/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [hsqrt, Complex.ofReal_mul]
  change _ = _ * (_ * ((1+(Real.exp t : ℂ)^2) *
    burnolDepthFeature (Real.log (p : ℝ)) n (Real.exp t)))
  ring

private theorem dense_evenWeightedColumn (p : Nat.Primes) (N : ℕ := 0) :
    Dense (Submodule.span ℂ (range (fun n => evenWeightedColumn (p,n+N))) : Set evenSubspace) := by
  have hd := primeBurnolEvenExtension.surjective.denseRange.dense_image
    primeBurnolEvenExtension.continuous (dense_weightedDepth p N)
  have hmap : Submodule.span ℂ (range (fun n => weightedDepth p (n+N))) ≤
      (Submodule.span ℂ (range (fun n => evenWeightedColumn (p,n+N)))).comap
        primeBurnolEvenExtension.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change primeBurnolEvenExtension (weightedDepth p (n+N)) ∈
      Submodule.span ℂ (range (fun n => evenWeightedColumn (p,n+N)))
    have hc : (Real.sqrt 2 : ℂ) * primeBurnolAmplitude (p,n+N) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne')
        (primeBurnolAmplitude_ne_zero (p,n+N))
    have heq : primeBurnolEvenExtension (weightedDepth p (n+N)) =
        ((Real.sqrt 2 : ℂ) * primeBurnolAmplitude (p,n+N))⁻¹ • evenWeightedColumn (p,n+N) := by
      rw [evenWeightedColumn_extension, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  apply hd.mono
  rintro _ ⟨x, hx, rfl⟩
  exact hmap hx

private def squareResolvent : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (φ := fun x : ℝ => ((1+x^2 : ℝ)⁻¹ : ℂ))
    (by fun_prop) zero_le_one (fun x => by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (inv_le_one₀ (by positivity)).mpr (by nlinarith [sq_nonneg x]))

private theorem squareResolvent_ae (h : SoninL2) :
    (squareResolvent h : ℝ → ℂ) =ᵐ[volume] fun x => ((1+x^2 : ℝ)⁻¹ : ℂ) * h x :=
  lpBoundedMulCLM_coeFn _ _ _ _

private theorem squareResolvent_sum (f : burnolSquarePosition.domain) :
    squareResolvent ((f : SoninL2) + burnolSquarePosition f) = (f : SoninL2) := by
  apply Lp.ext
  filter_upwards [squareResolvent_ae ((f : SoninL2) + burnolSquarePosition f),
    Lp.coeFn_add (f : SoninL2) (burnolSquarePosition f),
    maximalRealL2Mul_apply_ae volume (fun x : ℝ => x^2) f] with x hr ha hm
  change (burnolSquarePosition f) x = ((x^2 : ℝ) : ℂ) * (f : SoninL2) x at hm
  rw [hr, ha, Pi.add_apply, hm]
  have hn : ((1+x^2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  calc
    _ = ((1+x^2 : ℝ) : ℂ)⁻¹ * (((1+x^2 : ℝ) : ℂ) * (f : SoninL2) x) := by
      push_cast
      ring
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

private def squareGraphParam : SoninL2 →L[ℂ] (SoninL2 × SoninL2) :=
  squareResolvent.prod (ContinuousLinearMap.id ℂ SoninL2 - squareResolvent)

private theorem squareGraphParam_sum (f : burnolSquarePosition.domain) :
    squareGraphParam ((f : SoninL2) + burnolSquarePosition f) =
      ((f : SoninL2), burnolSquarePosition f) := by
  apply Prod.ext
  · exact squareResolvent_sum f
  · change ((f : SoninL2) + burnolSquarePosition f) -
      squareResolvent ((f : SoninL2) + burnolSquarePosition f) = burnolSquarePosition f
    rw [squareResolvent_sum]
    abel

/-- The literal graph columns retain the original prime-depth Euler amplitudes. -/
def primeBurnolSquareGraphCore (p : Nat.Primes) : Submodule ℂ (SoninL2 × SoninL2) :=
  Submodule.span ℂ (range (fun n =>
    (primeBurnolEvenFeatureLp (p,n), burnolSquarePosition (primeBurnolSquareColumn (p,n)))))

/-- Any depth tail retains its literal multiplication-graph columns. -/
def primeBurnolSquareGraphTailCore (p : Nat.Primes) (N : ℕ) : Submodule ℂ (SoninL2 × SoninL2) :=
  Submodule.span ℂ (range (fun n =>
    (primeBurnolEvenFeatureLp (p,n+N),burnolSquarePosition (primeBurnolSquareColumn (p,n+N)))))

theorem primeBurnolSquareGraphTailCore_le (p : Nat.Primes) (N : ℕ) :
    primeBurnolSquareGraphTailCore p N ≤ primeBurnolSquareGraphCore p := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n,rfl⟩
  exact Submodule.subset_span ⟨n+N,rfl⟩

/-- The entire maximal position-square graph on even physical input. -/
def primeBurnolEvenSquareGraph : Submodule ℂ (SoninL2 × SoninL2) :=
  burnolSquarePosition.graph ⊓ evenSubspace.prod ⊤

private theorem evenSquareGraph_closed :
    IsClosed (primeBurnolEvenSquareGraph : Set (SoninL2 × SoninL2)) := by
  have hm : IsClosed (burnolSquarePosition.graph : Set (SoninL2 × SoninL2)) :=
    (maximalRealL2Mul_isSelfAdjoint volume (by fun_prop : Measurable fun x : ℝ => x^2)).isClosed
  have he : IsClosed (evenSubspace : Set SoninL2) := by
    convert isClosed_eq l2Reflection.continuous continuous_id using 1
    ext v
    exact mem_evenSubspace_iff v
  exact hm.inter (he.prod isClosed_univ)

private theorem squareGraphCore_le (p : Nat.Primes) :
    primeBurnolSquareGraphCore p ≤ primeBurnolEvenSquareGraph := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact ⟨burnolSquarePosition.mem_graph (primeBurnolSquareColumn (p,n)),
    primeBurnolEvenFeatureLp_mem_evenSubspace (p,n), Submodule.mem_top⟩

/-- Every tail of one prime-depth tower is a core for the actual even maximal graph. -/
theorem primeBurnolSquareGraphTailCore_closure (p : Nat.Primes) (N : ℕ) :
    (primeBurnolSquareGraphTailCore p N).topologicalClosure = primeBurnolEvenSquareGraph := by
  apply le_antisymm
  · exact (primeBurnolSquareGraphTailCore p N).topologicalClosure_minimal
      ((primeBurnolSquareGraphTailCore_le p N).trans (squareGraphCore_le p)) evenSquareGraph_closed
  · intro z hz
    obtain ⟨f, hf, hM⟩ := (burnolSquarePosition.mem_graph_iff).mp hz.1
    have he : (f : SoninL2) ∈ evenSubspace := hf.symm ▸ hz.2.1
    let u : evenSubspace := ⟨(f : SoninL2) + burnolSquarePosition f,
      evenSubspace.add_mem he (burnolSquarePosition_mem_evenSubspace f he)⟩
    let G : evenSubspace →L[ℂ] (SoninL2 × SoninL2) :=
      squareGraphParam ∘L evenSubspace.subtypeL
    have hmem : ∀ v ∈ Submodule.span ℂ (range (fun n => evenWeightedColumn (p,n+N))),
        G v ∈ (primeBurnolSquareGraphTailCore p N).topologicalClosure := by
      change Submodule.span ℂ (range (fun n => evenWeightedColumn (p,n+N))) ≤
        ((primeBurnolSquareGraphTailCore p N).topologicalClosure).comap G.toLinearMap
      apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      change squareGraphParam ((primeBurnolSquareColumn (p,n+N) : SoninL2) +
        burnolSquarePosition (primeBurnolSquareColumn (p,n+N))) ∈
          (primeBurnolSquareGraphTailCore p N).topologicalClosure
      rw [squareGraphParam_sum (primeBurnolSquareColumn (p,n+N))]
      exact (primeBurnolSquareGraphTailCore p N).le_topologicalClosure (Submodule.subset_span ⟨n,rfl⟩)
    have hu := closure_minimal hmem
      ((primeBurnolSquareGraphTailCore p N).isClosed_topologicalClosure.preimage G.continuous)
      (dense_evenWeightedColumn p N u)
    change squareGraphParam ((f : SoninL2) + burnolSquarePosition f) ∈
      (primeBurnolSquareGraphTailCore p N).topologicalClosure at hu
    rw [squareGraphParam_sum, hf, hM] at hu
    exact hu

/-- Every single prime-depth tower is a core for the actual even maximal multiplication graph. -/
theorem primeBurnolSquareGraphCore_closure (p : Nat.Primes) :
    (primeBurnolSquareGraphCore p).topologicalClosure = primeBurnolEvenSquareGraph :=
  primeBurnolSquareGraphTailCore_closure p 0


/-- Continuous assembly from the two separately admitted multiplication graphs. -/
def burnolJetGraphAssembly : ((SoninL2 × SoninL2) × (SoninL2 × SoninL2)) →L[ℂ]
    ((SoninL2 × SoninL2) × (SoninL2 × SoninL2)) where
  toFun z := ((z.1.1, z.2.1), (z.1.1 + fourierUnitary z.2.1,
    z.1.2 + fourierUnitary z.2.2))
  map_add' z w := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel
  map_smul' c z := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
        RingHom.id_apply, smul_add]
  cont := by fun_prop

/-- Finite literal source graph, retaining both input coordinates and both Fourier–jet outputs. -/
def primeBurnolFourierJetPrimeGraph (p : Nat.Primes) :
    Submodule ℂ ((SoninL2 × SoninL2) × (SoninL2 × SoninL2)) :=
  ((primeBurnolSquareGraphCore p).prod (primeBurnolSquareGraphCore p)).map
    burnolJetGraphAssembly.toLinearMap

/-- Literal Fourier-jet graph using only depths at or beyond `N`. -/
def primeBurnolFourierJetTailGraph (p : Nat.Primes) (N : ℕ) :
    Submodule ℂ ((SoninL2 × SoninL2) × (SoninL2 × SoninL2)) :=
  ((primeBurnolSquareGraphTailCore p N).prod (primeBurnolSquareGraphTailCore p N)).map
    burnolJetGraphAssembly.toLinearMap

/-- Maximal-domain even source graph before closure, with the actual Fourier–jet synthesis. -/
def primeBurnolFourierJetEvenGraph :
    Submodule ℂ ((SoninL2 × SoninL2) × (SoninL2 × SoninL2)) :=
  (primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph).map
    burnolJetGraphAssembly.toLinearMap

/-- Every depth tail has the same graph completion as the even maximal source. -/
theorem primeBurnolFourierJetTailGraph_closure (p : Nat.Primes) (N : ℕ) :
    (primeBurnolFourierJetTailGraph p N).topologicalClosure =
      primeBurnolFourierJetEvenGraph.topologicalClosure := by
  have hprod : ((primeBurnolSquareGraphTailCore p N).prod
      (primeBurnolSquareGraphTailCore p N)).topologicalClosure =
      primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph := by
    apply SetLike.ext'
    change closure ((primeBurnolSquareGraphTailCore p N : Set (SoninL2 × SoninL2)) ×ˢ
      (primeBurnolSquareGraphTailCore p N : Set (SoninL2 × SoninL2))) = _
    rw [closure_prod_eq]
    change ((primeBurnolSquareGraphTailCore p N).topologicalClosure : Set (SoninL2 × SoninL2)) ×ˢ
      ((primeBurnolSquareGraphTailCore p N).topologicalClosure : Set (SoninL2 × SoninL2)) = _
    rw [primeBurnolSquareGraphTailCore_closure]
    rfl
  have hmap : primeBurnolFourierJetEvenGraph ≤
      (primeBurnolFourierJetTailGraph p N).topologicalClosure := by
    have h := ((primeBurnolSquareGraphTailCore p N).prod
      (primeBurnolSquareGraphTailCore p N)).topologicalClosure_map burnolJetGraphAssembly
    rw [hprod] at h
    exact h
  apply le_antisymm
  · apply (primeBurnolFourierJetTailGraph p N).topologicalClosure_minimal
      _ primeBurnolFourierJetEvenGraph.isClosed_topologicalClosure
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact primeBurnolFourierJetEvenGraph.le_topologicalClosure
      ⟨v, ⟨squareGraphCore_le p (primeBurnolSquareGraphTailCore_le p N hv.1),
        squareGraphCore_le p (primeBurnolSquareGraphTailCore_le p N hv.2)⟩, rfl⟩
  · exact primeBurnolFourierJetEvenGraph.topologicalClosure_minimal hmap
      (primeBurnolFourierJetTailGraph p N).isClosed_topologicalClosure

/-- The finite arithmetic core has exactly the same graph completion as the even maximal source. -/
theorem primeBurnolFourierJetPrimeGraph_closure (p : Nat.Primes) :
    (primeBurnolFourierJetPrimeGraph p).topologicalClosure =
      primeBurnolFourierJetEvenGraph.topologicalClosure :=
  primeBurnolFourierJetTailGraph_closure p 0

/-- Exact identification of the even source graph with the original maximal-domain synthesis. -/
theorem mem_primeBurnolFourierJetEvenGraph (w : (SoninL2 × SoninL2) × (SoninL2 × SoninL2)) :
    w ∈ primeBurnolFourierJetEvenGraph ↔
      ∃ f g : burnolSquarePosition.domain,
        (f : SoninL2) ∈ evenSubspace ∧ (g : SoninL2) ∈ evenSubspace ∧
        (((f : SoninL2), (g : SoninL2)), primeBurnolFourierJetSynthesis (f,g)) = w := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨f, hf, hM⟩ := burnolSquarePosition.mem_graph_iff.mp hz.1.1
    obtain ⟨g, hg, hN⟩ := burnolSquarePosition.mem_graph_iff.mp hz.2.1
    refine ⟨f, g, hf.symm ▸ hz.1.2.1, hg.symm ▸ hz.2.2.1, ?_⟩
    change (((f : SoninL2), (g : SoninL2)),
      ((f : SoninL2) + fourierUnitary (g : SoninL2),
       burnolSquarePosition f + fourierUnitary (burnolSquarePosition g))) = _
    rw [hf, hg, hM, hN]
    rfl
  · rintro ⟨f,g,hf,hg,rfl⟩
    exact ⟨(((f : SoninL2), burnolSquarePosition f),
      ((g : SoninL2), burnolSquarePosition g)),
      ⟨⟨burnolSquarePosition.mem_graph f, hf, Submodule.mem_top⟩,
       ⟨burnolSquarePosition.mem_graph g, hg, Submodule.mem_top⟩⟩, rfl⟩

/-- No bounded ambient output map recovers the first input on even one literal prime-depth core. -/
theorem primeBurnolFourierJetPrimeGraph_no_bounded_recovery (p : Nat.Primes) :
    ¬ ∃ R : (SoninL2 × SoninL2) →L[ℂ] SoninL2,
      ∀ w ∈ primeBurnolFourierJetPrimeGraph p, R w.2 = w.1.1 := by
  rintro ⟨R,hR⟩
  have hclosed : IsClosed {w : (SoninL2 × SoninL2) × (SoninL2 × SoninL2) |
      R w.2 = w.1.1} := isClosed_eq (by fun_prop) (by fun_prop)
  have hpass := closure_minimal hR hclosed
  apply primeBurnolFourierJet_no_bounded_even_recovery
  refine ⟨R, ?_⟩
  intro f g hf hg
  let w := (((f : SoninL2), (g : SoninL2)), primeBurnolFourierJetSynthesis (f,g))
  have hw : w ∈ primeBurnolFourierJetEvenGraph :=
    (mem_primeBurnolFourierJetEvenGraph w).mpr ⟨f,g,hf,hg,rfl⟩
  have hc : w ∈ (primeBurnolFourierJetPrimeGraph p).topologicalClosure := by
    rw [primeBurnolFourierJetPrimeGraph_closure]
    exact primeBurnolFourierJetEvenGraph.le_topologicalClosure hw
  exact hpass hc

end RHTower
