# Copyright (c) 2014, Guillaume Verdier <guillaume@verdier.info>
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# 1. Redistributions of source code must retain the above copyright notice, this
#    list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright notice,
#    this list of conditions and the following disclaimer in the documentation
#    and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
# ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

s|<span class="id" title="keyword">Proof</span>.\(<br/>\)*|<a class="proof" href="#">Show proof.</a><br/><div class="proof">|g
s|<span class="id" title="keyword">Next</span> <span class="id" title="keyword">Obligation</span>.\(<br/>\)*|<a class="proof" href="#">Show proof.</a><br/><div class="proof">|g
t goto-end-proof
b
:goto-end-proof
s|\(&nbsp;\)*<span class="id" title="keyword">Qed</span>.\(<br/>\)*|</div>|g
s|\(&nbsp;\)*<span class="id" title="keyword">Defined</span>.\(<br/>\)*|</div>|g
t
n
b goto-end-proof
