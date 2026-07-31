import GaloisForLFunctions.HTGeometry.FiniteRankTransportUnitary

/-!
# The Cayley limit of a nested exhaustion

A self-adjoint extension of a closed symmetric operator is recorded by its Cayley transform, which
splits as an orthogonal sum of the partial Cayley isometry of the operator itself and a unitary
boundary block on the deficiency spaces.  For a nested exhaustion the finite partial isometries are
all restrictions of the global one, so the embedded finite Cayley transform is

`V Q_a + W_a E_a`,

with `Q_a` the projection onto the finite range and `E_a` the projection onto the finite
deficiency space.

This module proves the two convergence statements that this decomposition supports.  Strong
convergence of the range and deficiency projections plus norm convergence of the boundary blocks
gives strong convergence of the assembled Cayley transforms; and conversely, once the automatic
base part is subtracted, strong convergence of the Cayley transforms is exactly strong convergence
of the boundary parts.  Through the Cayley resolvent formula both statements transfer verbatim to
generalized strong resolvent convergence across the varying finite spaces.

At deficiency index one the boundary block is one unit scalar times a rank-one transport, and the
norm convergence of the blocks is exactly convergence of that scalar phase.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ## The assembled Cayley transform -/

/-- The Cayley transform assembled from a base partial isometry `V` acting on the range part and a
boundary block `W` acting on the deficiency part. -/
def cayleyAssembly (V W Q Eb : E →L[𝕜] E) : E →L[𝕜] E := V ∘L Q + W ∘L Eb

@[simp] theorem cayleyAssembly_apply (V W Q Eb : E →L[𝕜] E) (x : E) :
    cayleyAssembly V W Q Eb x = V (Q x) + W (Eb x) := rfl

variable {ι : Type*} {l : Filter ι}

/-- **Existence half of the boundary-phase locking law.**  Strong convergence of the range and
deficiency projections together with norm convergence of the boundary blocks gives strong
convergence of the assembled Cayley transforms. -/
theorem tendsto_cayleyAssembly (V W : E →L[𝕜] E) {Q Eb Wa : ι → E →L[𝕜] E}
    {Qinf Ebinf : E →L[𝕜] E}
    (hQ : ∀ x, Tendsto (fun i => Q i x) l (𝓝 (Qinf x)))
    (hE : ∀ x, Tendsto (fun i => Eb i x) l (𝓝 (Ebinf x)))
    (hEb : ∀ i, ‖Eb i‖ ≤ 1)
    (hW : Tendsto (fun i => ‖Wa i - W‖) l (𝓝 0)) (x : E) :
    Tendsto (fun i => cayleyAssembly V (Wa i) (Q i) (Eb i) x) l
      (𝓝 (cayleyAssembly V W Qinf Ebinf x)) := by
  have hbase : Tendsto (fun i => V (Q i x)) l (𝓝 (V (Qinf x))) :=
    (V.continuous.continuousAt.tendsto).comp (hQ x)
  have hWcont : Tendsto (fun i => W (Eb i x)) l (𝓝 (W (Ebinf x))) :=
    (W.continuous.continuousAt.tendsto).comp (hE x)
  have hgap : Tendsto (fun i => (Wa i - W) (Eb i x)) l (𝓝 0) := by
    have hbound : ∀ i, ‖(Wa i - W) (Eb i x)‖ ≤ ‖Wa i - W‖ * ‖x‖ := by
      intro i
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      have := mul_le_mul_of_nonneg_right (hEb i) (norm_nonneg x)
      simpa using this
    have hzero : Tendsto (fun i => ‖Wa i - W‖ * ‖x‖) l (𝓝 0) := by
      simpa using hW.mul_const ‖x‖
    have := squeeze_zero (fun i => norm_nonneg _) hbound hzero
    exact tendsto_zero_iff_norm_tendsto_zero.mpr this
  have hboundary : Tendsto (fun i => Wa i (Eb i x)) l (𝓝 (W (Ebinf x))) := by
    have hsplit : ∀ i, Wa i (Eb i x) = (Wa i - W) (Eb i x) + W (Eb i x) := by
      intro i
      simp
    have := hgap.add hWcont
    rw [zero_add] at this
    exact this.congr fun i => (hsplit i).symm
  simpa using hbase.add hboundary

/-- **Classification half.**  Once the automatic base part is subtracted, strong convergence of
the assembled Cayley transforms is exactly strong convergence of the boundary parts. -/
theorem tendsto_boundary_of_tendsto_cayleyAssembly (V W : E →L[𝕜] E) {Q Eb Za : ι → E →L[𝕜] E}
    {Qinf Ebinf : E →L[𝕜] E}
    (hQ : ∀ x, Tendsto (fun i => Q i x) l (𝓝 (Qinf x)))
    (hC : ∀ x, Tendsto (fun i => cayleyAssembly V (Za i) (Q i) (Eb i) x) l
      (𝓝 (cayleyAssembly V W Qinf Ebinf x))) (x : E) :
    Tendsto (fun i => Za i (Eb i x)) l (𝓝 (W (Ebinf x))) := by
  have hbase : Tendsto (fun i => V (Q i x)) l (𝓝 (V (Qinf x))) :=
    (V.continuous.continuousAt.tendsto).comp (hQ x)
  have hsub := (hC x).sub hbase
  simpa using hsub

/-! ## Transfer to generalized strong resolvent convergence -/

/-- The Cayley resolvent formula.  For a self-adjoint `A` with Cayley transform `C`, one has
`(A + i)⁻¹ = (2i)⁻¹ (1 - C)`; the scalar is kept abstract so that the statement is independent of
the Cayley sign convention. -/
def cayleyResolvent (c : 𝕜) (C : E →L[𝕜] E) : E →L[𝕜] E := c • (1 - C)

/-- **Generalized strong resolvent convergence.**  If the ambient projections converge strongly to
the identity and the embedded Cayley transforms converge strongly, then the embedded resolvents
converge strongly to the global resolvent. -/
theorem tendsto_cayleyResolvent (c : 𝕜) {P Ca : ι → E →L[𝕜] E} {C : E →L[𝕜] E}
    (hP : ∀ x, Tendsto (fun i => P i x) l (𝓝 x))
    (hC : ∀ x, Tendsto (fun i => Ca i x) l (𝓝 (C x))) (x : E) :
    Tendsto (fun i => (c • (P i - Ca i)) x) l (𝓝 (cayleyResolvent c C x)) := by
  have hsub := (hP x).sub (hC x)
  have := hsub.const_smul c
  simpa [cayleyResolvent] using this

/-! ## Deficiency index one: the scalar phase lock -/

theorem norm_rankOneTransport (e f : E) :
    ‖rankOneTransport (𝕜 := 𝕜) e f‖ = ‖e‖ * ‖f‖ := by
  rw [rankOneTransport, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

theorem rankOneTransport_sub_left (a b c : E) :
    rankOneTransport (𝕜 := 𝕜) a c - rankOneTransport (𝕜 := 𝕜) b c
      = rankOneTransport (𝕜 := 𝕜) (a - b) c := by
  ext x
  simp [rankOneTransport, sub_smul]

theorem rankOneTransport_sub_right (a c d : E) :
    rankOneTransport (𝕜 := 𝕜) a c - rankOneTransport (𝕜 := 𝕜) a d
      = rankOneTransport (𝕜 := 𝕜) a (c - d) := by
  ext x
  simp [rankOneTransport, smul_sub]

/-- The rank-one transport is jointly continuous in operator norm. -/
theorem tendsto_opNorm_rankOneTransport_two {u v : ι → E} {e f : E}
    (hu : Tendsto u l (𝓝 e)) (hv : Tendsto v l (𝓝 f)) :
    Tendsto (fun i => ‖rankOneTransport (𝕜 := 𝕜) (u i) (v i)
      - rankOneTransport (𝕜 := 𝕜) e f‖) l (𝓝 0) := by
  have hsplit : ∀ i, rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f
      = rankOneTransport (𝕜 := 𝕜) (u i - e) (v i)
        + rankOneTransport (𝕜 := 𝕜) e (v i - f) := by
    intro i
    rw [← rankOneTransport_sub_left, ← rankOneTransport_sub_right]
    abel
  have hbound : ∀ i, ‖rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f‖
      ≤ ‖u i - e‖ * ‖v i‖ + ‖e‖ * ‖v i - f‖ := by
    intro i
    rw [hsplit i]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_rankOneTransport, norm_rankOneTransport]
  have hzero : Tendsto (fun i => ‖u i - e‖ * ‖v i‖ + ‖e‖ * ‖v i - f‖) l (𝓝 0) := by
    have h1 : Tendsto (fun i => ‖u i - e‖) l (𝓝 0) := by
      simpa using (hu.sub (tendsto_const_nhds (x := e))).norm
    have h2 : Tendsto (fun i => ‖v i - f‖) l (𝓝 0) := by
      simpa using (hv.sub (tendsto_const_nhds (x := f))).norm
    have h3 : Tendsto (fun i => ‖v i‖) l (𝓝 ‖f‖) := hv.norm
    have h4 : Tendsto (fun i => ‖u i - e‖ * ‖v i‖) l (𝓝 0) := by
      simpa using h1.mul h3
    have h5 : Tendsto (fun i => ‖e‖ * ‖v i - f‖) l (𝓝 0) := by
      simpa using h2.const_mul ‖e‖
    simpa using h4.add h5
  exact squeeze_zero (fun i => norm_nonneg _) hbound hzero

/-- **Phase lock, sufficiency.**  Converging phases and converging transported unit vectors give
boundary blocks converging in operator norm. -/
theorem tendsto_opNorm_phaseBlock {ζ : ι → 𝕜} {z : 𝕜} {u v : ι → E} {e f : E}
    (hζ : Tendsto ζ l (𝓝 z)) (hu : Tendsto u l (𝓝 e)) (hv : Tendsto v l (𝓝 f))
    (hbound : ∀ i, ‖ζ i‖ ≤ 1) :
    Tendsto (fun i => ‖ζ i • rankOneTransport (𝕜 := 𝕜) (u i) (v i)
      - z • rankOneTransport (𝕜 := 𝕜) e f‖) l (𝓝 0) := by
  have hsplit : ∀ i, ζ i • rankOneTransport (𝕜 := 𝕜) (u i) (v i)
      - z • rankOneTransport (𝕜 := 𝕜) e f
      = ζ i • (rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f)
        + (ζ i - z) • rankOneTransport (𝕜 := 𝕜) e f := by
    intro i
    rw [smul_sub, sub_smul]
    abel
  have hR := tendsto_opNorm_rankOneTransport_two (𝕜 := 𝕜) hu hv
  have hzeta : Tendsto (fun i => ‖ζ i - z‖) l (𝓝 0) := by
    simpa using (hζ.sub (tendsto_const_nhds (x := z))).norm
  have hbnd : ∀ i, ‖ζ i • rankOneTransport (𝕜 := 𝕜) (u i) (v i)
      - z • rankOneTransport (𝕜 := 𝕜) e f‖
      ≤ ‖rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f‖
        + ‖ζ i - z‖ * (‖e‖ * ‖f‖) := by
    intro i
    rw [hsplit i]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, norm_rankOneTransport]
    have h1 : ‖ζ i‖ * ‖rankOneTransport (𝕜 := 𝕜) (u i) (v i)
        - rankOneTransport (𝕜 := 𝕜) e f‖
        ≤ ‖rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f‖ := by
      have := mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg
        (rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f))
      simpa using this
    linarith
  have hzero : Tendsto (fun i =>
      ‖rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f‖
        + ‖ζ i - z‖ * (‖e‖ * ‖f‖)) l (𝓝 0) := by
    have := hzeta.mul_const (‖e‖ * ‖f‖)
    simpa using hR.add (by simpa using this)
  exact squeeze_zero (fun i => norm_nonneg _) hbnd hzero

/-- **Phase lock, necessity.**  Conversely, norm convergence of the boundary blocks between unit
transports forces the scalar phases to converge. -/
theorem tendsto_phase_of_tendsto_opNorm {ζ : ι → 𝕜} {z : 𝕜} {u v : ι → E} {e f : E}
    (hu : Tendsto u l (𝓝 e)) (hv : Tendsto v l (𝓝 f))
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hbound : ∀ i, ‖ζ i‖ ≤ 1)
    (hblock : Tendsto (fun i => ‖ζ i • rankOneTransport (𝕜 := 𝕜) (u i) (v i)
      - z • rankOneTransport (𝕜 := 𝕜) e f‖) l (𝓝 0)) :
    Tendsto ζ l (𝓝 z) := by
  have hR := tendsto_opNorm_rankOneTransport_two (𝕜 := 𝕜) hu hv
  have hsplit : ∀ i, (ζ i - z) • rankOneTransport (𝕜 := 𝕜) e f
      = (ζ i • rankOneTransport (𝕜 := 𝕜) (u i) (v i) - z • rankOneTransport (𝕜 := 𝕜) e f)
        - ζ i • (rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f) := by
    intro i
    rw [smul_sub, sub_smul]
    abel
  have hnorm : ∀ i, ‖ζ i - z‖
      ≤ ‖ζ i • rankOneTransport (𝕜 := 𝕜) (u i) (v i) - z • rankOneTransport (𝕜 := 𝕜) e f‖
        + ‖rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f‖ := by
    intro i
    have hval : ‖(ζ i - z) • rankOneTransport (𝕜 := 𝕜) e f‖ = ‖ζ i - z‖ := by
      rw [norm_smul, norm_rankOneTransport, he, hf]
      simp
    rw [← hval, hsplit i]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖ζ i • (rankOneTransport (𝕜 := 𝕜) (u i) (v i)
        - rankOneTransport (𝕜 := 𝕜) e f)‖
        ≤ ‖rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f‖ := by
      rw [norm_smul]
      have := mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg
        (rankOneTransport (𝕜 := 𝕜) (u i) (v i) - rankOneTransport (𝕜 := 𝕜) e f))
      simpa using this
    linarith
  have hzero : Tendsto (fun i => ‖ζ i - z‖) l (𝓝 0) :=
    squeeze_zero (fun i => norm_nonneg _) hnorm (by simpa using hblock.add hR)
  have := tendsto_zero_iff_norm_tendsto_zero.mpr hzero
  simpa using this.add_const z

end GaloisForLFunctions.HTGeometry
