---
title: The currying adjunction (2nd draft)
---
<div "style=display:none;">
$$\newcommand{cat}{\mathsf}%
\newcommand{id}{\mathrm{id}}%
\newcommand{bind}{\mathbin{\mathrm{\gg=}}}%
\newcommand{hom}{\mathrm{hom}}%
\newcommand{natto}{\Rightarrow}%{\stackrel{\bullet}{\to}}%
\newcommand{Id}{\mathrm{Id}}%
$$
</div>

Let $F$, $G$ be endofunctors of $\cat{Set}$, $F\dashv G$, with unit
$\eta$ and counit $\varepsilon$. Then there is a natural isomorphism
of sets, $\Phi_{AB} : \hom(FA, B)\cong\hom(A,GB)$, so if we choose a
singleton set $I=\{*\}$ for $A$, we obtain an isomorphism $\hom(FI,
B)\cong\hom(I,GB)\cong GB$. This means that $G$ is a representable
functor:

$$G \cong \hom(FI, -)$$

If we now apply the functor $\hom(A, -)$ and use the adjunction, we obtain

$$\hom(FA, B)\cong \hom(A, GB)\cong \hom(A,\hom(FI, B)) \cong
\hom(A\times FI, B),$$

by the Yoneda Lemma this implies an isomorphism

$$F \cong -\times FI.$$

This means that, up to isomorphism of functors, every pair of adjoint
functors in $\mathsf{Set}$ arises by choosing a set $S$ and defining
$FI := S$.

**Question**: Does that mean that the monad $M = GF$ with unit $\eta$ and
multiplication $\mu = G\bullet\varepsilon\bullet F$ is isomorphic to
the state monad with state $S$?

# Preparations

Let $S = FI$, and let $f = f^S : GF\natto \hom(S, -\times S)$ be the
isomorphism of functors mentioned before. In order to show that $f$ is
an isomorphism of monads, we must show that the following diagrams
commute

$$\require{AMScd}
\begin{CD}
GFGF @>{f\bullet f}>> \hom(S,\hom(S,-\times S)\times S)\\
@V{\mu}VV                     @V{\mu^S}VV \\
GF @>{f}>> \hom(S,-\times S)
\end{CD}
$$

and
$$\begin{CD}
\Id @= \Id\\
@V{\eta}VV @V{\eta^S}VV \\
GF @>{f}>> \hom(S,-\times S)
\end{CD}$$

where $\eta^S : \Id \natto \hom(S,-\times S)$ is the unit and $\mu^S :
\hom(S,\hom(S,-\times S)\times S)\natto\hom(S,-\times S)$ is the
multiplication of the state monad.

# Let's go

I'm going to compute an explicit representation of $f$ and check
directly whether the diagrams commute. This is going to be a bit of work...

First recall that the adjunction map arises from the unit and counit
as follows: $\Phi_{AB}(\varphi) = G(\varphi)\circ\eta_A$,
$\Phi_{AB}^{-1}(\psi) = \varepsilon_B\circ F(\psi)$.

For each set $A$, there is an isomorphism $e_A: \hom(I, A)\cong A$, $e_A(f) =
f(*)$, the evaluation at $*$. Therefore there is an isomorphism
$\alpha_B : \begin{CD}\hom(FI, B) @>{\Phi_{IB}}>> \hom(I, GB)
@>{e_{GB}}>> GB\end{CD}$, $\varphi\mapsto e_{GB}\left (
G(\varphi)\circ\eta_I \right ) = G(\varphi)(\eta_I(*))$. We're actually going to need the inverse of that, it's

$$\alpha_B^{-1} : GB \to \hom(FI, B)\\
y\mapsto \varepsilon_B\circ F(*\mapsto y).$$

Let $c^S_{AB} : \hom(A\times S, B)\cong\hom(A,\hom(S, B))$ denote the
curry map, $\varphi \mapsto (a\mapsto (a\mapsto \varphi(a,s)))$. It is
an adjunction map between $A\times -$ and $\hom(S, -)$. Then we obtain
an isomorphism

$$\hom(A\times FI, B)\to \hom(A,\hom(FI, B))\to \hom(A, GB)\to
\hom(FA, B),\\ \varphi \mapsto \varepsilon_B\circ F(a\mapsto
G(x\mapsto\varphi(a,x))(\eta_I(*))).$$

By applying it to the identity on $A\times FI$, we obtain an
isomorphism

$$\gamma_A : FA\cong A\times FI,\\
\gamma_A = \varepsilon \circ
F(a\mapsto G(x\mapsto (a,x))(\eta_I(*))).$$

We can now form the horizontal composition $f = \alpha^{-1}\bullet
\gamma : GF\natto \hom(FI, -\times FI)$. Recall the diagram

$$
\begin{CD}
GFA @>{G(\gamma_A)}>> G(A\times FI)\\
@V{\alpha^{-1}_{FA}}VV   @V{\alpha^{-1}_{A\times FI}}VV\\
\hom(FI, FA) @>{\hom(FI, \gamma_A)}>> \hom(FI, A\times FI)
\end{CD}$$

From the two ways to compute this map, the lower path seems to be more
approachable:

$$\begin{align*}
f_A(y) &= \gamma_A \circ \alpha^{-1}_{FA}(y)\\
&= \varepsilon_{A\times FI} \circ F(a\mapsto G(x\mapsto (a, x))(\eta_I(*))) \circ \varepsilon_{FA} \circ F(*\mapsto y)
\end{align*}
$$

This is getting ugly ...

# The "easy" part: Check compatibility with the unit

This is the condition $f_A(\eta_A(a)) = \eta^{FI})A(a) = (x\mapsto (a,
x))$ for all $a\in A$. Fearless as we are, let's apply $f_A$ to an argument:

$$f_A(\eta_A(a)) = \varepsilon_{A\times FI} \circ F(a\mapsto G(x\mapsto (a, x))(\eta_I(*))) \circ \varepsilon_{FA} \circ F(*\mapsto \eta_A(a))$$

It's time for little simplification. Let $\hat{a}$ denote the constant
map $*\mapsto a$. Then $*\mapsto \eta_A(a)$ can be written as
composition $\eta_A\circ \hat{a}$. This way, the part
$\varepsilon_{FA}\circ F(*\mapsto\eta_A(a))$ becomes $\varepsilon_{FA}
\circ F(\eta_A) \circ F(\hat{a})$, which is just $F(\hat{a})$ by the
triangle equation! We now have

$$
\begin{align*}
f_A(\eta_A(a)) &= \varepsilon_{A\times FI} \circ F(a\mapsto G(x\mapsto (a, x))(\eta_I(*))) \circ F(\hat{a})\\
&= \varepsilon_{A\times FI} \circ F(* \mapsto G(x\mapsto (a, x))(\eta_I(*)))\\
&= \varepsilon_{A\times FI} \circ F(G(x\mapsto (a,x))\circ\eta_I)\\
&= \varepsilon_{A\times FI} \circ FG(x\mapsto (a,x)) \circ F(\eta_I)
\end{align*}$$

Now use naturality of $\varepsilon$:

$$
\begin{align*}
f_A(\eta_A(a)) &= (x\mapsto (a,x)) \circ \varepsilon_{FI} \circ F(\eta_I)\\
&= (x\mapsto (a,x))\\
&= \eta^{FI}_A(a)
\end{align*}
$$

by the triangle equation again!

# Trembling now ... compatibility with multiplication

So now we have to check that $\mu^{FI}_A\circ(f\bullet f) =
f\circ\mu_A$, right? I'm afraid to tackle this directly. Each step
means scribbling more than a line of symbols where you easily lose
track of parentheses. There must be an easier way. Let's look at the
problem again, abstractly.

Say we have two adjoint pairs, $F\dashv G$ and $F'\dashv G'$, and
morphisms $\alpha: G\natto G'$ and $\beta : F\natto F'$, and we want
to prove that the following diagram commutes:

$$\begin{CD}
GFGF @>{\alpha\bullet\beta\bullet\alpha\bullet\beta}>> G'F'G'F'\\
@V{\mu}VV                                              @V{\mu'}VV\\
GF   @>{\alpha\bullet\beta}>>                          G'F'
\end{CD}$$

where $\mu = G\bullet\varepsilon\bullet F$ and $\mu' =
G'\bullet\varepsilon'\bullet F'$. We can employ the *interchange law*
between horizontal and vertical composition, which states (cited from MacLane[^MLNotation]) that

$$(\tau'\circ \sigma')\bullet(\tau\circ \sigma) = (\tau'\bullet\tau)\circ(\sigma'\bullet\sigma)$$

[^MLNotation]: Note that MacLane uses $\circ$ for horizontal and $\cdot$ for vertical composition.

if the compositions make sense. Let's apply this law:

$$\begin{align*}
\mu' \circ (\alpha\bullet\beta\bullet\alpha\bullet\beta) &= (G'\bullet\varepsilon'\bullet F')\circ(\alpha\bullet\beta\bullet\alpha\bullet\beta)\\
&= (G'\bullet(\varepsilon'\bullet F'))\circ(\alpha\bullet(\beta\bullet\alpha\bullet\beta))\\
&= (G'\circ\alpha) \bullet  ((\varepsilon'\bullet F')\circ ((\beta\bullet\alpha)\bullet\beta))\\
&= (G'\circ\alpha) \bullet (\varepsilon' \circ (\beta\bullet\alpha)) \bullet (F'\circ \beta)\\
&= \alpha \bullet (\varepsilon' \circ (\beta\bullet\alpha)) \bullet \beta\\
&\stackrel{?}{=} \alpha \bullet\varepsilon\bullet\beta\\
&= (\alpha\circ G)\bullet((\Id\bullet\Id)\circ \varepsilon)\bullet(\beta\circ F)\\
&= (\alpha\bullet\beta)\circ(G\bullet\varepsilon\bullet F)\\
&= (\alpha\bullet\beta)\circ\mu.
\end{align*}$$

We find that it suffices to prove $\varepsilon =
\varepsilon'\circ(\beta\bullet\alpha)$. In our case, that would be

$$\varepsilon = \varepsilon^{FI}\circ(\gamma\bullet\alpha^{-1}).$$

Let's keep the notation $G' = \hom(FI, -)$ and $F' = -\times FI$ for a bit. Recall then the natural transformations $\alpha : G'\natto G$ and $\gamma : F\natto F'$, where $\gamma_A$ is the composition

$$\begin{CD}
\hom(F'A, B) @>{\Phi'_{AB}}>> \hom(A, G'B) @>{\alpha_B\circ -}>> \hom(A, GB) @>{\Phi^{-1}_{AB}}>> \hom(FA, B)
\end{CD}$$

applied to $\id_{F'A}$, that is,

$$\begin{align*}
\gamma_A &= \Phi^{-1}_{A,F'A}(\alpha_{F'A}\circ \Phi'_{A,F'A}(\id_{F'A}))\\
&= \varepsilon_{F'A}\circ F(\alpha_{F'A}\circ \eta'_A)
\end{align*}.$$

Then

$$\begin{align*}
\varepsilon'_A \circ \gamma_{G'A} \circ F(\alpha^{-1}_A) &= \underline{\varepsilon'_A \circ \varepsilon_{F'G'A}} \circ F(\alpha_{F'G'A}\circ \eta'_{G'A} \circ \alpha^{-1}_A)\\
&= \varepsilon_A \circ FG(\varepsilon'_A) \circ F(\alpha_{F'G'A}\circ \eta'_{G'A} \circ \alpha^{-1}_A)\\
&= \varepsilon_A \circ F(\underline{G(\varepsilon'_A) \circ \alpha_{F'G'A}}\circ \eta'_{G'A} \circ \alpha^{-1}_A)\\
&= \varepsilon_A \circ F(\alpha_A\circ \underline{G'(\varepsilon'_A) \circ \eta'_{G'A}} \circ \alpha^{-1}_A)\\
&= \varepsilon_A \circ F(\alpha_A\circ \alpha^{-1}_A)\\
&= \varepsilon_A
\end{align*}$$

by naturality of $\varepsilon : FG\natto\Id$, $\alpha : G'\natto G$,
and the triangle equation $(G'\bullet\varepsilon') \circ (\eta'\bullet
G') = \id_{G'}$.

This concludes the proof. The morphism $f : GF\to \hom(FI, -\times FI)$ is an isomorphism of monads.
