We present a compositional framework for certifying resource bounds in typed programs.
Terms are typed with synthesized bounds b drawn from an abstract resource lattice (L,⪯
,⊕,⊥), enabling uniform treatment of time, memory, gas, and domain-specific costs. We
introduce a graded feasibility modality □r with counit and monotonicity laws. Our main
result is a syntactic cost soundness theorem: if a closed term has synthesized bound b under
budget r, its operational cost is bounded by b. We provide a cost-indexed semantic model
in the presheaf topos SetL where types are functors from bounds to value-cost pairs and
the cost function is a natural transformation to the internal lattice. We prove constructive
completeness via reification. A case study demonstrates end-to-end reasoning for binary
search. We discuss integration with Lean 4 via structural cost proxies and CI regression
testing.
